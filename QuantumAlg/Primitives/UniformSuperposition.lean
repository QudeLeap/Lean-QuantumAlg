/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.Gate.SupportHybrid
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.Encoded.BitGates
import all QuantumAlg.Primitives.WalshHadamard
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Non-power-of-two uniform superposition

This module fixes the source-level input certificate and the common semantic
and resource interface for a gate-level preparation of
`N = sum_j 2^ell_j`.  The intended schedule is Algorithm 1 of
Shukla and Vedula: an initial rotation, a lowest-block Hadamard layer, and
open-controlled rotations and Hadamards across the binary gaps
[SV24, Uniform.tex:622-664,775-805].
Its elementary-gate envelopes use the source's controlled-gate decompositions
[SV24, Uniform.tex:996-1024].

The `GateLevelCircuit` record deliberately carries one `UnitaryCircuit` tree.  Its
state equation, real-gate trace condition, and all resource bounds therefore
refer to the same execution object; a caller cannot attach a separate cost
certificate to an unrelated unitary.
-/

section

namespace QuantumAlg

namespace UniformSuperposition

open scoped BigOperators

open NormalizedVector Gate

noncomputable section

/-- The reciprocal square-root amplitude of a positive finite range. -/
def invSqrtCard (N : Nat) : ℂ :=
  (Real.sqrt (N : ℝ) : ℂ)⁻¹

theorem norm_sq_invSqrtCard {N : Nat} (hN : 0 < N) :
    ‖invSqrtCard N‖ ^ 2 = ((N : ℝ)⁻¹) := by
  rw [invSqrtCard, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (N : ℝ))]

/-- The normalized ket with equal amplitude on `0, ..., N - 1`. -/
def uniformState (N width : Nat) (hN : 0 < N)
    (hfits : N ≤ 2 ^ width) : NormalizedVector (Qubits width) :=
  NormalizedVector.ofVector
    (WithLp.toLp 2 fun i => if i.val < N then invSqrtCard N else 0)
    (by
      rw [EuclideanSpace.norm_eq]
      have hsum :
          ∑ i : Fin (2 ^ width),
              ‖if i.val < N then invSqrtCard N else 0‖ ^ 2 = 1 := by
        simp_rw [apply_ite, ite_pow, norm_zero,
          zero_pow (by omega : 2 ≠ 0)]
        rw [← Finset.sum_filter]
        rw [Finset.sum_const, Fin.card_filter_val_lt,
          min_eq_right hfits, nsmul_eq_mul,
          norm_sq_invSqrtCard hN]
        field_simp
      rw [hsum, Real.sqrt_one])

@[simp]
theorem uniformState_apply {N width : Nat} (hN : 0 < N)
    (hfits : N ≤ 2 ^ width) (i : Fin (2 ^ width)) :
    uniformState N width hN hfits i =
      if i.val < N then invSqrtCard N else 0 :=
  rfl

/-- A raw computational-basis ket at an arbitrary qubit width. -/
private def basisKetVec {width : Nat} (index : Fin (2 ^ width)) :
    HilbertVector (Qubits width) :=
  (NormalizedVector.ket (R := Qubits width) index :
    HilbertVector (Qubits width))

/-- The raw all-zero computational ket at an arbitrary qubit width. -/
private def rawKetZero (width : Nat) : HilbertVector (Qubits width) :=
  basisKetVec (width := width) 0

/-- A strictly increasing nonempty binary expansion of a positive integer.

`s >= 1` records the non-power-of-two case used by the preparation schedule;
there are `s + 1` set-bit exponents. -/
public structure BinaryExpansion (N : Nat) where
  /-- Number of binary gaps. -/
  s : Nat
  /-- At least two set bits occur. -/
  s_pos : 1 ≤ s
  /-- Set-bit exponents, in increasing order. -/
  ell : Fin (s + 1) → Nat
  /-- The bit positions are strictly increasing. -/
  ell_strict : StrictMono ell
  /-- The certified binary expansion. -/
  sum_powers : N = ∑ j, 2 ^ ell j
  /-- Positivity is retained explicitly for the normalized target state. -/
  N_pos : 0 < N

namespace BinaryExpansion

variable {N : Nat}

/-- Lowest set-bit exponent. -/
@[implicit_reducible]
def first (b : BinaryExpansion N) : Nat := b.ell 0

/-- Highest set-bit exponent. -/
@[implicit_reducible]
def last (b : BinaryExpansion N) : Nat := b.ell (Fin.last b.s)

/-- The preparation needs `last + 1` qubits. -/
@[implicit_reducible]
def width (b : BinaryExpansion N) : Nat := b.last + 1

/-- The binary sum fits its highest-bit width. -/
def fits (b : BinaryExpansion N) : Prop := N ≤ 2 ^ b.width

/-- The source upper bound for elementary one-qubit gates in one preparation
 [SV24, Uniform.tex:996-1024]. -/
def singleQubitBound (b : BinaryExpansion N) : Nat :=
  5 * b.s + 6 * b.last - 5 * b.first

/-- The source upper bound for CNOT gates in one preparation
 [SV24, Uniform.tex:996-1024]. -/
def cnotBound (b : BinaryExpansion N) : Nat :=
  b.last - b.first + 2 * b.s

/-- The sequential depth envelope for one preparation
 [SV24, Uniform.tex:996-1024]. -/
def depthBound (b : BinaryExpansion N) : Nat :=
  5 * (b.last - b.first) + 5 * b.s + 1

/-- The supplied increasing bit positions prove that the binary sum fits in
its intrinsic highest-bit width. -/
theorem fits_proof (b : BinaryExpansion N) : b.fits := by
  classical
  unfold fits
  calc
    N = ∑ j, 2 ^ b.ell j := b.sum_powers
    _ = ∑ exponent ∈ Finset.univ.image b.ell, 2 ^ exponent := by
      rw [Finset.sum_image]
      exact b.ell_strict.injective.injOn
    _ ≤ 2 ^ b.width :=
      (Nat.geomSum_lt (m := 2) (s := Finset.univ.image b.ell)
        (n := b.width) (by omega) (by
          intro exponent hexponent
          rcases Finset.mem_image.mp hexponent with ⟨j, -, rfl⟩
          unfold width last
          have hle : b.ell j ≤ b.ell (Fin.last b.s) :=
            b.ell_strict.monotone (Fin.le_last j)
          omega)).le

end BinaryExpansion

/-! ### Actual wire lifting

The source numbers qubits little-endian while the Core circuit layout is
big-endian.  The helpers below keep that conversion explicit: they extend a
literal one-qubit circuit by identities on either side, rather than treating a
logical reindexing as a free physical gate. -/

/-- Transport a circuit only across a proved equality of qubit widths.  This
is an index-level cast, not a physical wire permutation. -/
def castWidth {source target : Nat} (h : source = target)
    (program : UnitaryCircuit (Qubits source)) : UnitaryCircuit (Qubits target) :=
  h ▸ program

@[simp]
theorem castWidth_eventTrace {source target : Nat} (h : source = target)
    (program : UnitaryCircuit (Qubits source)) :
    (castWidth h program).eventTrace = program.eventTrace := by
  subst target
  rfl

@[simp]
theorem castWidth_eventCost {source target : Nat} (h : source = target)
    (program : UnitaryCircuit (Qubits source)) :
    (castWidth h program).eventCost = program.eventCost := by
  subst target
  rfl

@[simp]
theorem castWidth_eventDepth {source target : Nat} (h : source = target)
    (program : UnitaryCircuit (Qubits source)) :
    (castWidth h program).eventDepth = program.eventDepth := by
  subst target
  rfl

@[simp]
theorem castWidth_evaluatedEventDepth {source target : Nat}
    (h : source = target) (program : UnitaryCircuit (Qubits source))
    (assign : Resource.Event .quantum → Nat) :
    (castWidth h program).evaluatedEventDepth assign =
      program.evaluatedEventDepth assign := by
  subst target
  rfl

/-- Append a literal identity whose advertised footprint is the canonical
register range.  The identity contributes no event, matrix action, or depth;
it only makes a complete physical placement explicit for callers which join
this circuit to a larger register. -/
def withCanonicalFootprint {width : Nat} (program : UnitaryCircuit (Qubits width)) :
    UnitaryCircuit (Qubits width) :=
  UnitaryCircuit.seq program
    (UnitaryCircuit.identity (Qubits width) (List.range width) List.nodup_range)

@[simp]
theorem withCanonicalFootprint_eventTrace {width : Nat}
    (program : UnitaryCircuit (Qubits width)) :
    (withCanonicalFootprint program).eventTrace = program.eventTrace := by
  simp [withCanonicalFootprint]

@[simp]
theorem withCanonicalFootprint_eventCost {width : Nat}
    (program : UnitaryCircuit (Qubits width)) :
    (withCanonicalFootprint program).eventCost = program.eventCost := by
  simp [withCanonicalFootprint]

@[simp]
theorem withCanonicalFootprint_evaluatedEventDepth {width : Nat}
    (program : UnitaryCircuit (Qubits width))
    (assign : Resource.Event .quantum → Nat) :
    (withCanonicalFootprint program).evaluatedEventDepth assign =
      program.evaluatedEventDepth assign := by
  unfold withCanonicalFootprint
  rw [UnitaryCircuit.evaluatedEventDepth_seq]
  change program.evaluatedEventDepth assign +
      DepthExpr.depthEval assign (.id) = program.evaluatedEventDepth assign
  simp only [DepthExpr.depthEval_id, Nat.add_zero]

@[simp]
theorem castWidth_physical_idx {source target : Nat} (h : source = target)
    (program : UnitaryCircuit (Qubits source)) :
    (castWidth h program).physical_idx = program.physical_idx := by
  subst target
  rfl

@[simp]
theorem withCanonicalFootprint_applyNormalized {width : Nat}
    (program : UnitaryCircuit (Qubits width)) (state : NormalizedVector (Qubits width)) :
    (withCanonicalFootprint program).applyNormalized state =
      program.applyNormalized state := by
  simp [withCanonicalFootprint]

/-- A program already contained in the canonical carrier acquires exactly the
canonical full footprint after `withCanonicalFootprint`. -/
theorem withCanonicalFootprint_physical_idx {width : Nat}
    (program : UnitaryCircuit (Qubits width))
    (contained : program.physical_idx ⊆ List.range width) :
    (withCanonicalFootprint program).physical_idx = List.range width := by
  change UnitaryCircuit.unionPhysicalIdx program.physical_idx (List.range width) = _
  exact UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset _ _ contained

/-- Place a literal one-qubit circuit between an untouched left and right
qubit register. -/
def atMiddle (leftWidth rightWidth : Nat) (program : UnitaryCircuit (Qubits 1)) :
    UnitaryCircuit (Qubits (leftWidth + 1 + rightWidth)) :=
  UnitaryCircuit.prodLeft (n := rightWidth)
    (UnitaryCircuit.prodRight (m := leftWidth) program)

@[simp]
theorem atMiddle_eventTrace (leftWidth rightWidth : Nat)
    (program : UnitaryCircuit (Qubits 1)) :
    (atMiddle leftWidth rightWidth program).eventTrace = program.eventTrace := by
  simp [atMiddle]

@[simp]
theorem atMiddle_eventCost (leftWidth rightWidth : Nat)
    (program : UnitaryCircuit (Qubits 1)) :
    (atMiddle leftWidth rightWidth program).eventCost = program.eventCost := by
  simp [atMiddle]

@[simp]
theorem atMiddle_evaluatedEventDepth (leftWidth rightWidth : Nat)
    (program : UnitaryCircuit (Qubits 1)) (assign : Resource.Event .quantum → Nat) :
    (atMiddle leftWidth rightWidth program).evaluatedEventDepth assign =
      program.evaluatedEventDepth assign := by
  simp [atMiddle]

/-- A middle lifting of a canonically placed one-qubit program stays inside
the enlarged canonical register. -/
theorem atMiddle_physical_idx_subset_range (leftWidth rightWidth : Nat)
    (program : UnitaryCircuit (Qubits 1))
    (contained : program.physical_idx ⊆ List.range 1) :
    (atMiddle leftWidth rightWidth program).physical_idx ⊆
      List.range (leftWidth + 1 + rightWidth) := by
  unfold atMiddle
  apply UnitaryCircuit.prodLeft_physical_idx_subset_range
  exact UnitaryCircuit.prodRight_physical_idx_subset_range program contained

/-- Tensor semantics for an actual left-register lifting. -/
theorem prodLeft_applyNormalized_tensor {m n : Nat}
    (program : UnitaryCircuit (Qubits m)) (left : NormalizedVector (Qubits m))
    (right : NormalizedVector (Qubits n)) :
    (UnitaryCircuit.prodLeft (n := n) program).applyNormalized (left.tensor right) =
      (program.applyNormalized left).tensor right := by
  change ((UnitaryCircuit.prodLeft (n := n) program).matrix).apply
      (left.tensor right) = _
  rw [UnitaryCircuit.prodLeft, UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_apply_tensor]
  change (program.applyNormalized left).tensor
      ((UnitaryCircuit.identity (Qubits n) [] List.nodup_nil).applyNormalized right) = _
  rw [UnitaryCircuit.applyNormalized_identity]

/-- Tensor semantics for an actual right-register lifting. -/
theorem prodRight_applyNormalized_tensor {m n : Nat}
    (program : UnitaryCircuit (Qubits n)) (left : NormalizedVector (Qubits m))
    (right : NormalizedVector (Qubits n)) :
    (UnitaryCircuit.prodRight (m := m) program).applyNormalized (left.tensor right) =
      left.tensor (program.applyNormalized right) := by
  change ((UnitaryCircuit.prodRight (m := m) program).matrix).apply
      (left.tensor right) = _
  rw [UnitaryCircuit.prodRight, UnitaryCircuit.tensorQubits_matrix,
    UnitaryCircuit.shiftPhysicalIdx_matrix, UnitaryOperator.tensor_apply_tensor]
  change ((UnitaryCircuit.identity (Qubits m) [] List.nodup_nil).applyNormalized left).tensor
      (program.applyNormalized right) = _
  rw [UnitaryCircuit.applyNormalized_identity]

/-- Tensor action of a literal one-qubit circuit placed in the middle of a
three-register decomposition. -/
theorem atMiddle_applyNormalized_tensor {m n : Nat}
    (program : UnitaryCircuit (Qubits 1)) (left : NormalizedVector (Qubits m))
    (middle : NormalizedVector (Qubits 1))
    (right : NormalizedVector (Qubits n)) :
    (atMiddle m n program).applyNormalized ((left.tensor middle).tensor right) =
      (left.tensor (program.applyNormalized middle)).tensor right := by
  unfold atMiddle
  rw [prodLeft_applyNormalized_tensor, prodRight_applyNormalized_tensor]

/-- Raw-vector tensor form of `prodLeft_applyNormalized_tensor`. -/
theorem prodLeft_applyVec_tensor {m n : Nat}
    (program : UnitaryCircuit (Qubits m)) (left : HilbertVector (Qubits m))
    (right : HilbertVector (Qubits n)) :
    (UnitaryCircuit.prodLeft (n := n) program).applyVec (HilbertVector.tensor left right) =
      HilbertVector.tensor (program.applyVec left) right := by
  change ((UnitaryCircuit.prodLeft (n := n) program).matrix).applyVec
      (HilbertVector.tensor left right) = _
  rw [UnitaryCircuit.prodLeft, UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor (program.applyVec left)
      ((UnitaryCircuit.identity (Qubits n) [] List.nodup_nil).applyVec right) = _
  rw [UnitaryCircuit.applyVec_identity]

/-- Raw-vector tensor form of `prodRight_applyNormalized_tensor`. -/
theorem prodRight_applyVec_tensor {m n : Nat}
    (program : UnitaryCircuit (Qubits n)) (left : HilbertVector (Qubits m))
    (right : HilbertVector (Qubits n)) :
    (UnitaryCircuit.prodRight (m := m) program).applyVec (HilbertVector.tensor left right) =
      HilbertVector.tensor left (program.applyVec right) := by
  change ((UnitaryCircuit.prodRight (m := m) program).matrix).applyVec
      (HilbertVector.tensor left right) = _
  rw [UnitaryCircuit.prodRight, UnitaryCircuit.tensorQubits_matrix,
    UnitaryCircuit.shiftPhysicalIdx_matrix, UnitaryOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor
      ((UnitaryCircuit.identity (Qubits m) [] List.nodup_nil).applyVec left)
      (program.applyVec right) = _
  rw [UnitaryCircuit.applyVec_identity]

/-- Raw-vector tensor action of a literal one-qubit circuit placed in the
middle of a three-register split. -/
theorem atMiddle_applyVec_tensor {m n : Nat}
    (program : UnitaryCircuit (Qubits 1)) (left : HilbertVector (Qubits m))
    (middle : HilbertVector (Qubits 1))
    (right : HilbertVector (Qubits n)) :
    (atMiddle m n program).applyVec
        (HilbertVector.tensor (HilbertVector.tensor left middle) right) =
      HilbertVector.tensor (HilbertVector.tensor left (program.applyVec middle)) right := by
  unfold atMiddle
  rw [prodLeft_applyVec_tensor, prodRight_applyVec_tensor]

/-- Address a literal one-qubit circuit by its physical big-endian wire. -/
def atWire {width : Nat} (wire : Fin width) (program : UnitaryCircuit (Qubits 1)) :
    UnitaryCircuit (Qubits width) :=
  castWidth (by omega : wire.val + 1 + (width - wire.val - 1) = width)
    (atMiddle wire.val (width - wire.val - 1) program)

@[simp]
theorem atWire_eventTrace {width : Nat} (wire : Fin width)
    (program : UnitaryCircuit (Qubits 1)) :
    (atWire wire program).eventTrace = program.eventTrace := by
  simp [atWire]

@[simp]
theorem atWire_eventCost {width : Nat} (wire : Fin width)
    (program : UnitaryCircuit (Qubits 1)) :
    (atWire wire program).eventCost = program.eventCost := by
  simp [atWire]

@[simp]
theorem atWire_evaluatedEventDepth {width : Nat} (wire : Fin width)
    (program : UnitaryCircuit (Qubits 1)) (assign : Resource.Event .quantum → Nat) :
    (atWire wire program).evaluatedEventDepth assign =
      program.evaluatedEventDepth assign := by
  simp [atWire]

/-- Addressing a canonically placed one-qubit program never moves it outside
the full register carrier. -/
theorem atWire_physical_idx_subset_range {width : Nat} (wire : Fin width)
    (program : UnitaryCircuit (Qubits 1))
    (contained : program.physical_idx ⊆ List.range 1) :
    (atWire wire program).physical_idx ⊆ List.range width := by
  rw [atWire, castWidth_physical_idx]
  simpa only [show wire.val + 1 + (width - wire.val - 1) = width by omega] using
    (atMiddle_physical_idx_subset_range wire.val
      (width - wire.val - 1) program contained)

/-- Transport a normalized state only across a proved equality of widths. -/
def castWidthState {source target : Nat} (h : source = target)
    (state : NormalizedVector (Qubits source)) :
    NormalizedVector (Qubits target) :=
  h ▸ state

/-- Equality transport for an unnormalized Hilbert vector. -/
def castWidthVec {source target : Nat} (h : source = target)
    (state : HilbertVector (Qubits source)) : HilbertVector (Qubits target) :=
  h ▸ state

/-- The corresponding cast on computational-basis labels.  Keeping this
transport explicit is useful when a tensor-shaped raw ket is lifted back to
the full physical width. -/
def castWidthIndex {source target : Nat} (h : source = target)
    (index : Fin (2 ^ source)) : Fin (2 ^ target) :=
  Fin.cast (by subst target; rfl) index

@[simp]
theorem castWidthIndex_val {source target : Nat} (h : source = target)
    (index : Fin (2 ^ source)) : (castWidthIndex h index).val = index.val := by
  subst target
  rfl

@[simp]
theorem castWidthIndex_symm {source target : Nat} (h : source = target)
    (index : Fin (2 ^ target)) :
    castWidthIndex h (castWidthIndex h.symm index) = index := by
  subst target
  rfl

@[simp]
private theorem castWidthVec_ket {source target : Nat} (h : source = target)
    (index : Fin (2 ^ source)) :
    castWidthVec h (basisKetVec index) =
      basisKetVec (castWidthIndex h index) := by
  subst target
  rfl

@[simp]
private theorem castWidthVec_rawKetZero {source target : Nat}
    (h : source = target) :
    castWidthVec h (rawKetZero source) = rawKetZero target := by
  unfold rawKetZero
  rw [castWidthVec_ket]
  congr 1

@[simp]
private theorem castWidthVec_self {width : Nat}
    (state : HilbertVector (Qubits width)) :
    castWidthVec rfl state = state :=
  rfl

private theorem castWidthVec_walshUniform {source target : Nat}
    (h : source = target) :
    castWidthVec h
        (WalshHadamard.uniformState source : HilbertVector (Qubits source)) =
      (WalshHadamard.uniformState target : HilbertVector (Qubits target)) := by
  subst target
  rfl

/-- Pointwise form of raw-vector width transport. -/
@[simp]
theorem castWidthVec_apply {source target : Nat} (h : source = target)
    (state : HilbertVector (Qubits source)) (index : Fin (2 ^ target)) :
    castWidthVec h state index = state (castWidthIndex h.symm index) := by
  subst target
  rfl

@[simp]
theorem castWidth_applyVec {source target : Nat} (h : source = target)
    (program : UnitaryCircuit (Qubits source))
    (state : HilbertVector (Qubits source)) :
    (castWidth h program).applyVec (castWidthVec h state) =
      castWidthVec h (program.applyVec state) := by
  subst target
  rfl

/-- Width transport is linear on raw state vectors.  The Algorithm-1
residual induction keeps its branches unnormalised, so these small transport
facts let the literal tensor lift distribute over the two rotation branches
without introducing a semantic wrapper. -/
@[simp]
theorem castWidthVec_add {source target : Nat} (h : source = target)
    (left right : HilbertVector (Qubits source)) :
    castWidthVec h (left + right) =
      castWidthVec h left + castWidthVec h right := by
  subst target
  rfl

@[simp]
theorem castWidthVec_smul {source target : Nat} (h : source = target)
    (scalar : ℂ) (state : HilbertVector (Qubits source)) :
    castWidthVec h (scalar • state) = scalar • castWidthVec h state := by
  subst target
  rfl

/-- Width casts distribute through a concrete raw tensor whenever the two
factor widths are transported independently.  This is merely equality
transport, so its proof reduces after substituting the two width equalities. -/
private theorem castWidthVec_tensor
    {leftSource leftTarget rightSource rightTarget : Nat}
    (hleft : leftSource = leftTarget) (hright : rightSource = rightTarget)
    (left : HilbertVector (Qubits leftSource))
    (right : HilbertVector (Qubits rightSource)) :
    castWidthVec (by
      subst leftTarget
      subst rightTarget
      rfl : leftSource + rightSource = leftTarget + rightTarget)
      (HilbertVector.tensor left right) =
      HilbertVector.tensor (castWidthVec hleft left) (castWidthVec hright right) := by
  subst leftTarget
  subst rightTarget
  rfl

/-- Consecutive width transports compose to their transitive equality. -/
private theorem castWidthVec_trans {source middle target : Nat}
    (first : source = middle) (second : middle = target)
    (state : HilbertVector (Qubits source)) :
    castWidthVec second (castWidthVec first state) =
      castWidthVec (first.trans second) state := by
  subst middle
  subst target
  rfl

/-- A width transport followed by its inverse is the identity on raw
vectors. -/
private theorem castWidthVec_symm {source target : Nat}
    (h : source = target) (state : HilbertVector (Qubits source)) :
    castWidthVec h.symm (castWidthVec h state) = state := by
  subst target
  rfl

/-- Transporting the left factor before tensoring is the same as transporting
the completed tensor.  This keeps the Algorithm-1 factorization proof from
accumulating equality casts one register at a time. -/
private theorem castWidthVec_tensor_left_transport
    {leftSource leftTarget rightWidth targetWidth : Nat}
    (hleft : leftSource = leftTarget)
    (htarget : leftTarget + rightWidth = targetWidth)
    (left : HilbertVector (Qubits leftSource))
    (right : HilbertVector (Qubits rightWidth)) :
    castWidthVec htarget (HilbertVector.tensor (castWidthVec hleft left) right) =
      castWidthVec (by
        subst leftTarget
        exact htarget : leftSource + rightWidth = targetWidth)
        (HilbertVector.tensor left right) := by
  subst leftTarget
  rfl

/-- Right-factor counterpart of `castWidthVec_tensor_left_transport`. -/
private theorem castWidthVec_tensor_right_transport
    {leftWidth rightSource rightTarget targetWidth : Nat}
    (hright : rightSource = rightTarget)
    (htarget : leftWidth + rightTarget = targetWidth)
    (left : HilbertVector (Qubits leftWidth))
    (right : HilbertVector (Qubits rightSource)) :
    castWidthVec htarget (HilbertVector.tensor left (castWidthVec hright right)) =
      castWidthVec (by
        subst rightTarget
        exact htarget : leftWidth + rightSource = targetWidth)
        (HilbertVector.tensor left right) := by
  subst rightTarget
  rfl

/-- Two surrounding right-associated tensor factors preserve an inner width
transport.  It is the bookkeeping bridge from a gap's unsplit zero block to
its `middle ⊗ target` form. -/
private theorem castWidthVec_tensor_two_right_transport
    {highWidth innerLeftWidth sourceWidth targetWidth finalWidth : Nat}
    (hinner : sourceWidth = targetWidth)
    (hsource : highWidth + (innerLeftWidth + sourceWidth) = finalWidth)
    (htarget : highWidth + (innerLeftWidth + targetWidth) = finalWidth)
    (high : HilbertVector (Qubits highWidth))
    (innerLeft : HilbertVector (Qubits innerLeftWidth))
    (source : HilbertVector (Qubits sourceWidth)) :
    castWidthVec hsource
      (HilbertVector.tensor high (HilbertVector.tensor innerLeft source)) =
      castWidthVec htarget
        (HilbertVector.tensor high
          (HilbertVector.tensor innerLeft (castWidthVec hinner source))) := by
  subst targetWidth
  rfl

/-- Three surrounding right-associated tensor factors preserve an inner
width transport.  This is used when an expanded `|+⟩` block is moved through
the still-zero portion of a source gap. -/
private theorem castWidthVec_tensor_three_right_transport
    {highWidth firstWidth middleWidth sourceWidth targetWidth finalWidth : Nat}
    (hinner : sourceWidth = targetWidth)
    (hsource : highWidth + (firstWidth + (middleWidth + sourceWidth)) = finalWidth)
    (htarget : highWidth + (firstWidth + (middleWidth + targetWidth)) = finalWidth)
    (high : HilbertVector (Qubits highWidth))
    (first : HilbertVector (Qubits firstWidth))
    (middle : HilbertVector (Qubits middleWidth))
    (source : HilbertVector (Qubits sourceWidth)) :
    castWidthVec hsource
      (HilbertVector.tensor high
        (HilbertVector.tensor first (HilbertVector.tensor middle source))) =
      castWidthVec htarget
        (HilbertVector.tensor high
          (HilbertVector.tensor first
            (HilbertVector.tensor middle (castWidthVec hinner source)))) := by
  subst targetWidth
  rfl

/-- Raw-vector action of an actual one-qubit circuit embedded at an arbitrary
physical wire.  The two surrounding factors are retained explicitly, so the
Algorithm-1 proof can use the literal wire placement rather than a free
register reindexing. -/
theorem atWire_applyVec_tensor {width : Nat} (wire : Fin width)
    (program : UnitaryCircuit (Qubits 1))
    (left : HilbertVector (Qubits wire.val))
    (middle : HilbertVector (Qubits 1))
    (right : HilbertVector (Qubits (width - wire.val - 1))) :
    (atWire wire program).applyVec
        (castWidthVec (by omega : wire.val + 1 + (width - wire.val - 1) = width)
          (HilbertVector.tensor (HilbertVector.tensor left middle) right)) =
      castWidthVec (by omega : wire.val + 1 + (width - wire.val - 1) = width)
        (HilbertVector.tensor (HilbertVector.tensor left (program.applyVec middle)) right) := by
  unfold atWire
  rw [castWidth_applyVec, atMiddle_applyVec_tensor]

@[simp]
theorem castWidth_applyNormalized {source target : Nat} (h : source = target)
    (program : UnitaryCircuit (Qubits source))
    (state : NormalizedVector (Qubits source)) :
    (castWidth h program).applyNormalized (castWidthState h state) =
      castWidthState h (program.applyNormalized state) := by
  subst target
  rfl

@[simp]
theorem castWidthState_ket_zero {source target : Nat} (h : source = target) :
    castWidthState h (NormalizedVector.ket (R := Qubits source) 0) =
      NormalizedVector.ket (R := Qubits target) 0 := by
  subst target
  rfl

/-- Transport a normalized state along a logical index equivalence.  This is
the state-side counterpart of `UnitaryCircuit.reindex`; it only changes the carrier
coordinates and carries no execution event. -/
def reindexState {source target : Nat}
    (equiv : Fin (2 ^ source) ≃ Fin (2 ^ target))
    (state : NormalizedVector (Qubits source)) :
    NormalizedVector (Qubits target) :=
  NormalizedVector.ofVector
    (WithLp.toLp 2 fun i => state (equiv.symm i))
    (by
      rw [EuclideanSpace.norm_eq]
      rw [← Equiv.sum_comp equiv
        (fun i => ‖state (equiv.symm i)‖ ^ 2)]
      simp only [Equiv.symm_apply_apply]
      simpa only [EuclideanSpace.norm_eq] using state.norm_eq_one)

@[simp]
theorem reindexState_apply {source target : Nat}
    (equiv : Fin (2 ^ source) ≃ Fin (2 ^ target))
    (state : NormalizedVector (Qubits source)) (index : Fin (2 ^ target)) :
    reindexState equiv state index = state (equiv.symm index) :=
  rfl

/-- Raw-vector counterpart of `reindexState`, used when the Algorithm-1
induction splits a normalized state into its two orthogonal branches. -/
def reindexVec {source target : Nat}
    (equiv : Fin (2 ^ source) ≃ Fin (2 ^ target))
    (state : HilbertVector (Qubits source)) : HilbertVector (Qubits target) :=
  WithLp.toLp 2 fun index => state (equiv.symm index)

@[simp]
theorem reindexVec_apply {source target : Nat}
    (equiv : Fin (2 ^ source) ≃ Fin (2 ^ target))
    (state : HilbertVector (Qubits source)) (index : Fin (2 ^ target)) :
    reindexVec equiv state index = state (equiv.symm index) :=
  rfl

@[simp]
theorem reindexVec_add {source target : Nat}
    (equiv : Fin (2 ^ source) ≃ Fin (2 ^ target))
    (left right : HilbertVector (Qubits source)) :
    reindexVec equiv (left + right) =
      reindexVec equiv left + reindexVec equiv right := by
  apply WithLp.ofLp_injective
  funext index
  rfl

@[simp]
theorem reindexVec_smul {source target : Nat}
    (equiv : Fin (2 ^ source) ≃ Fin (2 ^ target))
    (scalar : ℂ) (state : HilbertVector (Qubits source)) :
    reindexVec equiv (scalar • state) = scalar • reindexVec equiv state := by
  apply WithLp.ofLp_injective
  funext index
  rfl

/-- Raw computational basis kets commute with a logical index reindexing. -/
private theorem reindexVec_ket {source target : Nat}
    (equiv : Fin (2 ^ source) ≃ Fin (2 ^ target))
    (index : Fin (2 ^ source)) :
    reindexVec equiv (basisKetVec index) = basisKetVec (equiv index) := by
  apply WithLp.ofLp_injective
  funext output
  simp [reindexVec, basisKetVec, NormalizedVector.ket_apply,
    Equiv.symm_apply_eq]

/-- The raw tensor of two computational-basis kets is their concrete
big-endian product label. -/
private theorem raw_tensor_ket {m n : Nat}
    (left : Fin (2 ^ m)) (right : Fin (2 ^ n)) :
    HilbertVector.tensor
        (basisKetVec left) (basisKetVec right) =
      basisKetVec (prodEquiv (m := m) (n := n) (left, right)) := by
  simpa [basisKetVec] using congrArg
    (fun state : NormalizedVector (Qubits (m + n)) =>
      (state : HilbertVector (Qubits (m + n))))
    (NormalizedVector.tensor_ket left right)

/-- The all-zero raw ket is stable under a concrete product split. -/
private theorem raw_tensor_ket0 {m n : Nat} :
    HilbertVector.tensor
      (rawKetZero m) (rawKetZero n) = rawKetZero (m + n) := by
  unfold rawKetZero
  rw [raw_tensor_ket]
  congr 1

/-- The all-zero tensor identity with an explicit target-width transport.
This is the small dependent-width bridge used when one source gap is split
at its next physical target. -/
private theorem raw_tensor_ket0_cast {m n target : Nat} (h : m + n = target) :
    castWidthVec h
      (HilbertVector.tensor (rawKetZero m) (rawKetZero n)) =
      rawKetZero target := by
  subst target
  exact raw_tensor_ket0

/-- A zero-width all-zero factor is a genuine tensor identity on raw
vectors.  It is used only to erase the empty outer factors introduced by the
literal separated-wire lifting. -/
private theorem raw_ket0_tensor_left_zero {n : Nat}
    (state : HilbertVector (Qubits n)) :
    castWidthVec (Nat.zero_add n)
      (HilbertVector.tensor (m := 0) (n := n) (rawKetZero 0) state) = state := by
  apply WithLp.ofLp_injective
  funext index
  rw [castWidthVec_apply]
  have hindex : castWidthIndex (Nat.zero_add n).symm index =
      prodEquiv (m := 0) (n := n) (0, index) := by
    apply Fin.ext
    simp [prodEquiv, finProdFinEquiv]
  rw [hindex, HilbertVector.tensor_apply_prod]
  simp [rawKetZero, basisKetVec, NormalizedVector.ket_apply]

private theorem raw_ket0_tensor_left_of_eq_zero {m n : Nat}
    (hm : m = 0) (state : HilbertVector (Qubits n)) :
    castWidthVec (by omega : m + n = n)
        (HilbertVector.tensor (rawKetZero m) state) = state := by
  subst m
  exact raw_ket0_tensor_left_zero state

/-- A zero-width all-zero suffix is a genuine tensor identity on raw
vectors. -/
private theorem raw_ket0_tensor_right_zero {n : Nat}
    (state : HilbertVector (Qubits n)) :
    HilbertVector.tensor (m := n) (n := 0) state (rawKetZero 0) = state := by
  apply WithLp.ofLp_injective
  funext index
  have hindex : index = prodEquiv (m := n) (n := 0) (index, 0) := by
    apply Fin.ext
    simp [prodEquiv, finProdFinEquiv]
  rw [hindex, HilbertVector.tensor_apply_prod]
  simp [rawKetZero, basisKetVec, NormalizedVector.ket_apply, prodEquiv, finProdFinEquiv]

private theorem castWidthVec_raw_ket0_both_zero {n target : Nat}
    (h : n = target) (state : HilbertVector (Qubits n)) :
    castWidthVec (by omega : (0 + n) + 0 = target)
        (HilbertVector.tensor
          (HilbertVector.tensor (rawKetZero 0) state) (rawKetZero 0)) =
      castWidthVec h state := by
  subst target
  rw [raw_ket0_tensor_right_zero]
  simpa using raw_ket0_tensor_left_zero state

/-- Appending a physical `|+⟩` to a Walsh-uniform raw block gives the
next-width Walsh-uniform block. -/
private theorem walshUniform_tensor_ketPlus (n : Nat) :
    HilbertVector.tensor
        (WalshHadamard.uniformState n : HilbertVector (Qubits n))
        (ketPlus : HilbertVector (Qubits 1)) =
      (WalshHadamard.uniformState (n + 1) : HilbertVector (Qubits (n + 1))) := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := n) (n := 1)).surjective index with
    ⟨⟨left, right⟩, rfl⟩
  simp only [HilbertVector.tensor_apply_prod,
    WalshHadamard.uniformState_apply, NormalizedVector.ketPlus_apply]
  rw [WalshHadamard.invSqrtCard_succ]

/-- The same Walsh factorization with the newly expanded physical qubit on
the left.  This is the orientation induced by Algorithm 1's right-to-left
gap schedule. -/
private theorem ketPlus_tensor_walshUniform (n : Nat) :
    HilbertVector.tensor
        (ketPlus : HilbertVector (Qubits 1))
        (WalshHadamard.uniformState n : HilbertVector (Qubits n)) =
      (WalshHadamard.uniformState (1 + n) : HilbertVector (Qubits (1 + n))) := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := 1) (n := n)).surjective index with
    ⟨⟨left, right⟩, rfl⟩
  simp only [HilbertVector.tensor_apply_prod,
    WalshHadamard.uniformState_apply, NormalizedVector.ketPlus_apply]
  rw [show 1 + n = n + 1 by omega, WalshHadamard.invSqrtCard_succ]
  ring

/-- Normalize the associativity cast which appears when a leading control
is tensored with a rightmost target qubit. -/
private theorem castWidthVec_ket0_tensor_ketPlus (n : Nat) :
    castWidthVec (by omega : (1 + n) + 1 = (n + 1) + 1)
      (HilbertVector.tensor
        (rawKetZero (1 + n))
        (ketPlus : HilbertVector (Qubits 1))) =
      HilbertVector.tensor
        (rawKetZero (n + 1))
        (ketPlus : HilbertVector (Qubits 1)) := by
  rw [castWidthVec_tensor (by omega : 1 + n = n + 1) rfl]
  simp only [castWidthVec_rawKetZero, castWidthVec_self]

/-- The right-to-left sequence of gap Hadamards builds this literal product
of `|+⟩` factors.  It is retained as a raw vector because the intermediate
Algorithm-1 branches are not normalized individually. -/
private def gapPlusBlock : (count : Nat) → HilbertVector (Qubits count)
  | 0 => rawKetZero 0
  | count + 1 =>
      castWidthVec (by omega : 1 + count = count + 1)
        (HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1))
          (gapPlusBlock count))

/-- The literal `|+⟩` product built by a gap layer is the ordinary Walsh
uniform block of the same width. -/
private theorem gapPlusBlock_eq_walshUniform (count : Nat) :
    gapPlusBlock count =
      (WalshHadamard.uniformState count : HilbertVector (Qubits count)) := by
  induction count with
  | zero =>
      apply WithLp.ofLp_injective
      funext index
      fin_cases index
      simp [gapPlusBlock, rawKetZero, basisKetVec,
        WalshHadamard.uniformState_apply,
        WalshHadamard.invSqrtCard]
  | succ count induction =>
      rw [gapPlusBlock, induction]
      have hfactor := ketPlus_tensor_walshUniform count
      rw [hfactor]
      apply WithLp.ofLp_injective
      funext index
      rw [castWidthVec_apply]
      simp only [WalshHadamard.uniformState_apply]
      simp [show 1 + count = count + 1 by omega]

/-- The concrete big-endian product encoding has its standard natural-number
address formula. -/
private theorem prodEquiv_val {leftWidth rightWidth : Nat}
    (left : Fin (2 ^ leftWidth)) (right : Fin (2 ^ rightWidth)) :
    (prodEquiv (m := leftWidth) (n := rightWidth) (left, right)).val =
      right.val + 2 ^ rightWidth * left.val :=
  rfl

/-- Explicit reassociation of raw qubit tensors.  Width equality is carried
by `castWidthVec`; the coordinate proof is the associativity of the concrete
big-endian `prodEquiv` address formula. -/
private theorem raw_tensor_assoc {m n p : Nat}
    (left : HilbertVector (Qubits m)) (middle : HilbertVector (Qubits n))
    (right : HilbertVector (Qubits p)) :
    castWidthVec (by omega : (m + n) + p = m + (n + p))
      (HilbertVector.tensor (HilbertVector.tensor left middle) right) =
      HilbertVector.tensor left (HilbertVector.tensor middle right) := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := m) (n := n + p)).surjective index with
    ⟨⟨leftIndex, rightIndex⟩, rfl⟩
  rcases (prodEquiv (m := n) (n := p)).surjective rightIndex with
    ⟨⟨middleIndex, rightIndex⟩, rfl⟩
  have hindex :
      castWidthIndex (by omega : m + (n + p) = (m + n) + p)
        (prodEquiv (m := m) (n := n + p)
          (leftIndex, prodEquiv (m := n) (n := p) (middleIndex, rightIndex))) =
        prodEquiv (m := m + n) (n := p)
          (prodEquiv (m := m) (n := n) (leftIndex, middleIndex), rightIndex) := by
    apply Fin.ext
    simp only [castWidthIndex_val, prodEquiv_val]
    rw [pow_add]
    ring
  rw [castWidthVec_apply, hindex]
  simp only [HilbertVector.tensor_apply_prod]
  ring

/-- One more explicit `|+⟩` factor from the gap-H sweep can be moved across
an arbitrary low suffix without changing physical bit order. -/
private theorem gapPlusBlock_succ_tensor_suffix (count suffixWidth : Nat)
    (suffix : HilbertVector (Qubits suffixWidth)) :
    castWidthVec (by omega :
      (count + 1) + suffixWidth = 1 + (count + suffixWidth))
      (HilbertVector.tensor (gapPlusBlock (count + 1)) suffix) =
      HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1))
        (HilbertVector.tensor (gapPlusBlock count) suffix) := by
  rw [gapPlusBlock]
  rw [castWidthVec_tensor_left_transport
    (by omega : 1 + count = count + 1)
    (by omega : (count + 1) + suffixWidth = 1 + (count + suffixWidth))]
  simpa using
    (raw_tensor_assoc (ketPlus : HilbertVector (Qubits 1))
      (gapPlusBlock count) suffix)

/-- Tensoring two Walsh-uniform raw vectors concatenates their physical
registers. -/
private theorem walshUniform_tensor_walshUniform (leftWidth rightWidth : Nat) :
    HilbertVector.tensor
        (WalshHadamard.uniformState leftWidth : HilbertVector (Qubits leftWidth))
        (WalshHadamard.uniformState rightWidth : HilbertVector (Qubits rightWidth)) =
      (WalshHadamard.uniformState (leftWidth + rightWidth) :
        HilbertVector (Qubits (leftWidth + rightWidth))) := by
  have hinv : WalshHadamard.invSqrtCard leftWidth *
      WalshHadamard.invSqrtCard rightWidth =
        WalshHadamard.invSqrtCard (leftWidth + rightWidth) := by
    unfold WalshHadamard.invSqrtCard
    rw [← mul_inv, ← Complex.ofReal_mul,
      ← Real.sqrt_mul (by positivity : 0 ≤ ((2 ^ leftWidth : Nat) : ℝ)),
      ← Nat.cast_mul, ← pow_add]
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := leftWidth) (n := rightWidth)).surjective index with
    ⟨⟨leftIndex, rightIndex⟩, rfl⟩
  simp only [HilbertVector.tensor_apply_prod,
    WalshHadamard.uniformState_apply]
  exact hinv

/-- A five-factor rebracketing used by the active Algorithm-1 gap step.
Both sides retain the concrete big-endian `prodEquiv` order
`high, first, middle, second, suffix`; the only work is equality transport
between parenthesized register widths. -/
private theorem raw_tensor_rebracket5 {highWidth middleWidth suffixWidth : Nat}
    (high : HilbertVector (Qubits highWidth))
    (first : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits middleWidth))
    (second : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits suffixWidth)) :
    castWidthVec (by omega :
      (highWidth + (1 + middleWidth)) + (1 + suffixWidth) =
        highWidth + (1 + (middleWidth + (1 + suffixWidth))) )
      (HilbertVector.tensor
        (HilbertVector.tensor high (HilbertVector.tensor first middle))
        (HilbertVector.tensor second suffix)) =
      castWidthVec (by omega :
        (highWidth + ((1 + middleWidth) + 1)) + suffixWidth =
          highWidth + (1 + (middleWidth + (1 + suffixWidth))))
        (HilbertVector.tensor
          (HilbertVector.tensor high
            (HilbertVector.tensor (HilbertVector.tensor first middle) second))
          suffix) := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := highWidth)
    (n := 1 + (middleWidth + (1 + suffixWidth)))).surjective index with
    ⟨⟨highIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))).surjective
      tailIndex with ⟨⟨firstIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := middleWidth) (n := 1 + suffixWidth)).surjective
      tailIndex with ⟨⟨middleIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := suffixWidth)).surjective tailIndex with
    ⟨⟨secondIndex, suffixIndex⟩, rfl⟩
  have hleft :
      castWidthIndex (by omega :
        highWidth + (1 + (middleWidth + (1 + suffixWidth))) =
          (highWidth + (1 + middleWidth)) + (1 + suffixWidth))
        (prodEquiv (m := highWidth)
          (n := 1 + (middleWidth + (1 + suffixWidth)))
          (highIndex,
            prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))
              (firstIndex,
                prodEquiv (m := middleWidth) (n := 1 + suffixWidth)
                  (middleIndex,
                    prodEquiv (m := 1) (n := suffixWidth)
                      (secondIndex, suffixIndex))))) =
        prodEquiv (m := highWidth + (1 + middleWidth))
          (n := 1 + suffixWidth)
          ((prodEquiv (m := highWidth) (n := 1 + middleWidth)
            (highIndex, prodEquiv (m := 1) (n := middleWidth)
              (firstIndex, middleIndex))),
            prodEquiv (m := 1) (n := suffixWidth)
              (secondIndex, suffixIndex)) := by
    apply Fin.ext
    simp only [castWidthIndex_val, prodEquiv_val]
    rw [pow_add, pow_add, pow_add]
    ring
  have hright :
      castWidthIndex (by omega :
        highWidth + (1 + (middleWidth + (1 + suffixWidth))) =
          (highWidth + ((1 + middleWidth) + 1)) + suffixWidth)
        (prodEquiv (m := highWidth)
          (n := 1 + (middleWidth + (1 + suffixWidth)))
          (highIndex,
            prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))
              (firstIndex,
                prodEquiv (m := middleWidth) (n := 1 + suffixWidth)
                  (middleIndex,
                    prodEquiv (m := 1) (n := suffixWidth)
                      (secondIndex, suffixIndex))))) =
        prodEquiv (m := highWidth + ((1 + middleWidth) + 1))
          (n := suffixWidth)
          ((prodEquiv (m := highWidth) (n := (1 + middleWidth) + 1)
            (highIndex,
              prodEquiv (m := 1 + middleWidth) (n := 1)
                (prodEquiv (m := 1) (n := middleWidth)
                  (firstIndex, middleIndex), secondIndex))),
            suffixIndex) := by
    apply Fin.ext
    simp only [castWidthIndex_val, prodEquiv_val]
    rw [pow_add, pow_add, pow_add]
    ring
  rw [castWidthVec_apply, hleft, castWidthVec_apply, hright]
  simp only [HilbertVector.tensor_apply_prod]
  ring

/-- Five-factor rebracketing for the first (uncontrolled) source rotation:
the physical target is isolated as the last factor of the high register. -/
private theorem raw_tensor_rotation5 {highWidth middleWidth suffixWidth : Nat}
    (high : HilbertVector (Qubits highWidth))
    (first : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits middleWidth))
    (second : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits suffixWidth)) :
    castWidthVec (by omega :
      (highWidth + (1 + middleWidth)) + (1 + suffixWidth) =
        highWidth + (1 + (middleWidth + (1 + suffixWidth))))
      (HilbertVector.tensor
        (HilbertVector.tensor high (HilbertVector.tensor first middle))
        (HilbertVector.tensor second suffix)) =
      castWidthVec (by omega :
        (highWidth + 1) + (middleWidth + (1 + suffixWidth)) =
          highWidth + (1 + (middleWidth + (1 + suffixWidth))))
        (HilbertVector.tensor
          (HilbertVector.tensor high first)
          (HilbertVector.tensor middle
            (HilbertVector.tensor second suffix))) := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := highWidth)
    (n := 1 + (middleWidth + (1 + suffixWidth)))).surjective index with
    ⟨⟨highIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))).surjective
      tailIndex with ⟨⟨firstIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := middleWidth) (n := 1 + suffixWidth)).surjective
      tailIndex with ⟨⟨middleIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := suffixWidth)).surjective tailIndex with
    ⟨⟨secondIndex, suffixIndex⟩, rfl⟩
  have hleft :
      castWidthIndex (by omega :
        highWidth + (1 + (middleWidth + (1 + suffixWidth))) =
          (highWidth + (1 + middleWidth)) + (1 + suffixWidth))
        (prodEquiv (m := highWidth)
          (n := 1 + (middleWidth + (1 + suffixWidth)))
          (highIndex,
            prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))
              (firstIndex,
                prodEquiv (m := middleWidth) (n := 1 + suffixWidth)
                  (middleIndex,
                    prodEquiv (m := 1) (n := suffixWidth)
                      (secondIndex, suffixIndex))))) =
        prodEquiv (m := highWidth + (1 + middleWidth))
          (n := 1 + suffixWidth)
          ((prodEquiv (m := highWidth) (n := 1 + middleWidth)
            (highIndex, prodEquiv (m := 1) (n := middleWidth)
              (firstIndex, middleIndex))),
            prodEquiv (m := 1) (n := suffixWidth)
              (secondIndex, suffixIndex)) := by
    apply Fin.ext
    simp only [castWidthIndex_val, prodEquiv_val]
    rw [pow_add, pow_add, pow_add]
    ring
  have hright :
      castWidthIndex (by omega :
        highWidth + (1 + (middleWidth + (1 + suffixWidth))) =
          (highWidth + 1) + (middleWidth + (1 + suffixWidth)))
        (prodEquiv (m := highWidth)
          (n := 1 + (middleWidth + (1 + suffixWidth)))
          (highIndex,
            prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))
              (firstIndex,
                prodEquiv (m := middleWidth) (n := 1 + suffixWidth)
                  (middleIndex,
                    prodEquiv (m := 1) (n := suffixWidth)
                      (secondIndex, suffixIndex))))) =
        prodEquiv (m := highWidth + 1)
          (n := middleWidth + (1 + suffixWidth))
          (prodEquiv (m := highWidth) (n := 1) (highIndex, firstIndex),
            prodEquiv (m := middleWidth) (n := 1 + suffixWidth)
              (middleIndex,
                prodEquiv (m := 1) (n := suffixWidth)
                  (secondIndex, suffixIndex))) := by
    apply Fin.ext
    simp only [castWidthIndex_val, prodEquiv_val]
    rw [pow_add, pow_add, pow_add]
    ring
  rw [castWidthVec_apply, hleft, castWidthVec_apply, hright]
  simp only [HilbertVector.tensor_apply_prod]
  ring

/-- Direct five-factor reassociation from the right-associated form used by
the residual invariant to the target-isolated form consumed by `atWire`.
This coordinate proof keeps all five physical factors in order and avoids any
logical wire reindexing in the first source rotation. -/
private theorem raw_tensor_right_to_rotation5
    {highWidth middleWidth suffixWidth : Nat}
    (high : HilbertVector (Qubits highWidth))
    (first : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits middleWidth))
    (second : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits suffixWidth)) :
    HilbertVector.tensor high
        (HilbertVector.tensor first
          (HilbertVector.tensor middle
            (HilbertVector.tensor second suffix))) =
      castWidthVec (by omega :
        (highWidth + 1) + (middleWidth + (1 + suffixWidth)) =
          highWidth + (1 + (middleWidth + (1 + suffixWidth))))
        (HilbertVector.tensor
          (HilbertVector.tensor high first)
          (HilbertVector.tensor middle
            (HilbertVector.tensor second suffix))) := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := highWidth)
    (n := 1 + (middleWidth + (1 + suffixWidth)))).surjective index with
    ⟨⟨highIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))).surjective
      tailIndex with ⟨⟨firstIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := middleWidth) (n := 1 + suffixWidth)).surjective
      tailIndex with ⟨⟨middleIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := suffixWidth)).surjective tailIndex with
    ⟨⟨secondIndex, suffixIndex⟩, rfl⟩
  have hindex :
      castWidthIndex (by omega :
        highWidth + (1 + (middleWidth + (1 + suffixWidth))) =
          (highWidth + 1) + (middleWidth + (1 + suffixWidth)))
        (prodEquiv (m := highWidth)
          (n := 1 + (middleWidth + (1 + suffixWidth)))
          (highIndex,
            prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))
              (firstIndex,
                prodEquiv (m := middleWidth) (n := 1 + suffixWidth)
                  (middleIndex,
                    prodEquiv (m := 1) (n := suffixWidth)
                      (secondIndex, suffixIndex))))) =
        prodEquiv (m := highWidth + 1)
          (n := middleWidth + (1 + suffixWidth))
          (prodEquiv (m := highWidth) (n := 1) (highIndex, firstIndex),
            prodEquiv (m := middleWidth) (n := 1 + suffixWidth)
              (middleIndex,
                prodEquiv (m := 1) (n := suffixWidth)
                  (secondIndex, suffixIndex))) := by
    apply Fin.ext
    simp only [castWidthIndex_val, prodEquiv_val]
    rw [pow_add, pow_add, pow_add]
    ring
  rw [castWidthVec_apply, hindex]
  simp only [HilbertVector.tensor_apply_prod]
  ring

/-- Transport the target-isolated five-factor tensor to the exact factor
widths required by `atWire`.  After the three width equalities are
substituted this is definitionally the same raw tensor; it records no
permutation and introduces no circuit operation. -/
private theorem raw_tensor_rotation5_transport
    {highWidth middleWidth suffixWidth leftWidth rightWidth targetWidth : Nat}
    (hleft : highWidth = leftWidth)
    (hright : middleWidth + (1 + suffixWidth) = rightWidth)
    (hraw : (highWidth + 1) + (middleWidth + (1 + suffixWidth)) = targetWidth)
    (hwhole : leftWidth + 1 + rightWidth = targetWidth)
    (high : HilbertVector (Qubits highWidth))
    (first : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits middleWidth))
    (second : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits suffixWidth)) :
    castWidthVec hraw
      (HilbertVector.tensor
        (HilbertVector.tensor high first)
        (HilbertVector.tensor middle
          (HilbertVector.tensor second suffix))) =
      castWidthVec hwhole
        (HilbertVector.tensor
          (HilbertVector.tensor (castWidthVec hleft high) first)
          (castWidthVec hright
            (HilbertVector.tensor middle
              (HilbertVector.tensor second suffix)))) := by
  subst leftWidth
  subst rightWidth
  subst targetWidth
  rfl

/-- The same five physical factors, from the fully right-associated form
produced by a suffix tensor to the form exposed by `atSeparatedVec`. -/
private theorem raw_tensor_right_to_separated5
    {highWidth middleWidth suffixWidth : Nat}
    (high : HilbertVector (Qubits highWidth))
    (first : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits middleWidth))
    (second : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits suffixWidth)) :
    HilbertVector.tensor high
        (HilbertVector.tensor first
          (HilbertVector.tensor middle
            (HilbertVector.tensor second suffix))) =
      castWidthVec (by omega :
        (highWidth + ((1 + middleWidth) + 1)) + suffixWidth =
          highWidth + (1 + (middleWidth + (1 + suffixWidth))))
        (HilbertVector.tensor
          (HilbertVector.tensor high
            (HilbertVector.tensor (HilbertVector.tensor first middle) second))
          suffix) := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := highWidth)
    (n := 1 + (middleWidth + (1 + suffixWidth)))).surjective index with
    ⟨⟨highIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))).surjective
      tailIndex with ⟨⟨firstIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := middleWidth) (n := 1 + suffixWidth)).surjective
      tailIndex with ⟨⟨middleIndex, tailIndex⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := suffixWidth)).surjective tailIndex with
    ⟨⟨secondIndex, suffixIndex⟩, rfl⟩
  have hindex :
      castWidthIndex (by omega :
        highWidth + (1 + (middleWidth + (1 + suffixWidth))) =
          (highWidth + ((1 + middleWidth) + 1)) + suffixWidth)
        (prodEquiv (m := highWidth)
          (n := 1 + (middleWidth + (1 + suffixWidth)))
          (highIndex,
            prodEquiv (m := 1) (n := middleWidth + (1 + suffixWidth))
              (firstIndex,
                prodEquiv (m := middleWidth) (n := 1 + suffixWidth)
                  (middleIndex,
                    prodEquiv (m := 1) (n := suffixWidth)
                      (secondIndex, suffixIndex))))) =
        prodEquiv (m := highWidth + ((1 + middleWidth) + 1))
          (n := suffixWidth)
          ((prodEquiv (m := highWidth) (n := (1 + middleWidth) + 1)
            (highIndex,
              prodEquiv (m := 1 + middleWidth) (n := 1)
                (prodEquiv (m := 1) (n := middleWidth)
                  (firstIndex, middleIndex), secondIndex))),
            suffixIndex) := by
    apply Fin.ext
    simp only [castWidthIndex_val, prodEquiv_val]
    rw [pow_add, pow_add, pow_add]
    ring
  rw [castWidthVec_apply, hindex]
  simp only [HilbertVector.tensor_apply_prod]
  ring

/-- Splitting a zero block of width `m + 1` immediately before an arbitrary
suffix exposes the final zero qubit without changing physical bit order. -/
private theorem raw_ket0_succ_tensor_suffix {middleWidth suffixWidth : Nat}
    (suffix : HilbertVector (Qubits suffixWidth)) :
    castWidthVec (by omega :
      (middleWidth + 1) + suffixWidth = middleWidth + (1 + suffixWidth))
      (HilbertVector.tensor
        (rawKetZero (middleWidth + 1)) suffix) =
      HilbertVector.tensor (rawKetZero middleWidth)
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix) := by
  rw [← raw_tensor_ket0]
  simpa [rawKetZero, basisKetVec, ket0] using
    (raw_tensor_assoc (rawKetZero middleWidth)
      (rawKetZero 1) suffix)

/-- Raw-vector insertion of an untouched middle register. -/
def insertMiddleVec {leftWidth middleWidth rightWidth : Nat}
    (state : HilbertVector (Qubits (leftWidth + rightWidth)))
    (middle : HilbertVector (Qubits middleWidth)) :
    HilbertVector (Qubits (leftWidth + middleWidth + rightWidth)) :=
  reindexVec (UnitaryCircuit.insertMiddleIndexEquiv leftWidth middleWidth rightWidth)
    (HilbertVector.tensor state middle)

/-- The explicit middle-register insertion sends a basis tensor on the two
outer one-qubit fields to the corresponding three-field basis tensor. -/
private theorem insertMiddleVec_tensor_ket {middleWidth : Nat}
    (first second : Fin (2 ^ 1)) (middle : Fin (2 ^ middleWidth)) :
    insertMiddleVec
        (HilbertVector.tensor
          (basisKetVec first) (basisKetVec second))
        (basisKetVec middle) =
      HilbertVector.tensor
        (HilbertVector.tensor
          (basisKetVec first) (basisKetVec middle))
        (basisKetVec second) := by
  unfold insertMiddleVec
  rw [raw_tensor_ket, raw_tensor_ket, reindexVec_ket,
    raw_tensor_ket, raw_tensor_ket]
  congr 1
  simp [UnitaryCircuit.insertMiddleIndexEquiv]

/-- The raw middle-insertion transport is the concrete associativity map for
three tensor factors.  Unlike the basis-only lemma above, this form keeps all
three fields arbitrary and is the local bridge used by the gap-H induction. -/
private theorem insertMiddleVec_tensor {leftWidth middleWidth rightWidth : Nat}
    (left : HilbertVector (Qubits leftWidth))
    (middle : HilbertVector (Qubits middleWidth))
    (right : HilbertVector (Qubits rightWidth)) :
    insertMiddleVec (HilbertVector.tensor left right) middle =
      HilbertVector.tensor (HilbertVector.tensor left middle) right := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := leftWidth + middleWidth) (n := rightWidth)).surjective
      index with ⟨⟨leftMiddle, rightIndex⟩, rfl⟩
  rcases (prodEquiv (m := leftWidth) (n := middleWidth)).surjective leftMiddle
      with ⟨⟨leftIndex, middleIndex⟩, rfl⟩
  simp only [insertMiddleVec, reindexVec_apply,
    HilbertVector.tensor_apply_prod]
  simp [UnitaryCircuit.insertMiddleIndexEquiv]
  ring

/-- Logical circuit reindexing commutes with raw-vector transport. -/
theorem reindex_applyVec {source target : Nat}
    (equiv : Fin (2 ^ source) ≃ Fin (2 ^ target))
    (program : UnitaryCircuit (Qubits source))
    (state : HilbertVector (Qubits source)) :
    (UnitaryCircuit.reindex equiv program).applyVec (reindexVec equiv state) =
      reindexVec equiv (program.applyVec state) := by
  apply WithLp.ofLp_injective
  funext output
  simp only [UnitaryCircuit.applyVec, UnitaryOperator.applyVec_apply,
    UnitaryCircuit.reindex_matrix, UnitaryOperator.coe_reindex,
    Matrix.reindex_apply, Matrix.submatrix_apply, reindexVec_apply]
  rw [← Equiv.sum_comp equiv
    (fun input =>
      (program.matrix : HilbertOperator (Qubits source))
        (equiv.symm output) (equiv.symm input) * state (equiv.symm input))]
  simp only [Equiv.symm_apply_apply]

/-- Raw-vector transport commutes with a reindexed mathematical unitary.  This
is the operator-level analogue of `reindex_applyVec` and is used below to
derive the physical right-control branch equations from its explicit swap
reindexing. -/
theorem unitary_reindex_applyVec {source target : Nat}
    (equiv : Fin (2 ^ source) ≃ Fin (2 ^ target))
    (program : UnitaryOperator (Qubits source))
    (state : HilbertVector (Qubits source)) :
    (UnitaryOperator.reindex equiv program).applyVec
        (reindexVec equiv state) =
      reindexVec equiv (program.applyVec state) := by
  apply WithLp.ofLp_injective
  funext output
  simp only [UnitaryOperator.applyVec_apply, UnitaryOperator.coe_reindex,
    Matrix.reindex_apply,
    Matrix.submatrix_apply, reindexVec_apply]
  rw [← Equiv.sum_comp equiv
    (fun input =>
      (program : HilbertOperator (Qubits source))
        (equiv.symm output) (equiv.symm input) * state (equiv.symm input))]
  simp only [Equiv.symm_apply_apply]

/-- A logical circuit reindex commutes with its explicit state transport.
This follows by reindexing the finite matrix-vector sum, so it is a semantic
lemma about the literal circuit rather than a basis-only realization rule. -/
theorem reindex_applyNormalized {source target : Nat}
    (equiv : Fin (2 ^ source) ≃ Fin (2 ^ target))
    (program : UnitaryCircuit (Qubits source))
    (state : NormalizedVector (Qubits source)) :
    (UnitaryCircuit.reindex equiv program).applyNormalized (reindexState equiv state) =
      reindexState equiv (program.applyNormalized state) := by
  apply NormalizedVector.ext
  intro output
  change (UnitaryCircuit.reindex equiv program).applyVec
      (reindexVec equiv (state : HilbertVector (Qubits source))) output =
    reindexVec equiv
      (program.applyVec (state : HilbertVector (Qubits source))) output
  exact congrArg (fun vector : HilbertVector (Qubits target) => vector output)
    (reindex_applyVec equiv program (state : HilbertVector (Qubits source)))

/-- Insert an untouched middle register into an arbitrary normalized
left/right state.  Unlike the public basis-endpoint lemma, this definition
retains the full superposed state required by Algorithm 1. -/
def insertMiddleState {leftWidth middleWidth rightWidth : Nat}
    (state : NormalizedVector (Qubits (leftWidth + rightWidth)))
    (middle : NormalizedVector (Qubits middleWidth)) :
    NormalizedVector (Qubits (leftWidth + middleWidth + rightWidth)) :=
  reindexState (UnitaryCircuit.insertMiddleIndexEquiv leftWidth middleWidth rightWidth)
    (state.tensor middle)

/-- Inserting an untouched middle register commutes with applying the actual
left/right circuit on an arbitrary normalized state. -/
theorem insertMiddle_applyNormalized_state
    {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit (Qubits (leftWidth + rightWidth)))
    (state : NormalizedVector (Qubits (leftWidth + rightWidth)))
    (middle : NormalizedVector (Qubits middleWidth)) :
    (UnitaryCircuit.insertMiddle (leftWidth := leftWidth) (middleWidth := middleWidth)
        (rightWidth := rightWidth) program).applyNormalized
        (insertMiddleState state middle) =
      insertMiddleState (program.applyNormalized state) middle := by
  unfold insertMiddleState
  unfold UnitaryCircuit.insertMiddle
  dsimp
  rw [UnitaryCircuit.Realizes.applyNormalized_relabel,
    reindex_applyNormalized, prodLeft_applyNormalized_tensor]

/-- Raw insertion is linear in the state carried by its two outer fields. -/
@[simp]
theorem insertMiddleVec_add {leftWidth middleWidth rightWidth : Nat}
    (left right : HilbertVector (Qubits (leftWidth + rightWidth)))
    (middle : HilbertVector (Qubits middleWidth)) :
    insertMiddleVec (left + right) middle =
      insertMiddleVec left middle + insertMiddleVec right middle := by
  unfold insertMiddleVec
  rw [HilbertVector.add_tensor, reindexVec_add]

@[simp]
theorem insertMiddleVec_smul {leftWidth middleWidth rightWidth : Nat}
    (scalar : ℂ) (state : HilbertVector (Qubits (leftWidth + rightWidth)))
    (middle : HilbertVector (Qubits middleWidth)) :
    insertMiddleVec (scalar • state) middle =
      scalar • insertMiddleVec state middle := by
  unfold insertMiddleVec
  rw [HilbertVector.smul_tensor, reindexVec_smul]

/-- Raw-vector form of the actual middle insertion action. -/
theorem insertMiddle_applyVec
    {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit (Qubits (leftWidth + rightWidth)))
    (state : HilbertVector (Qubits (leftWidth + rightWidth)))
    (middle : HilbertVector (Qubits middleWidth)) :
    (UnitaryCircuit.insertMiddle (leftWidth := leftWidth) (middleWidth := middleWidth)
        (rightWidth := rightWidth) program).applyVec
        (insertMiddleVec state middle) =
      insertMiddleVec (program.applyVec state) middle := by
  unfold insertMiddleVec
  unfold UnitaryCircuit.insertMiddle
  dsimp
  rw [UnitaryCircuit.relabel_applyVec,
    reindex_applyVec, prodLeft_applyVec_tensor]

/-- A fit is monotone under high-zero padding. -/
theorem fits_pad {N source target : Nat} (hfits : N ≤ 2 ^ source)
    (hwidth : source ≤ target) : N ≤ 2 ^ target :=
  hfits.trans (Nat.pow_le_pow_right (by norm_num) hwidth)

/-- `uniformState` is stable under a high all-zero tensor factor. -/
theorem ket0_tensor_uniformState_pad {N padding width : Nat} (hN : 0 < N)
    (hfits : N ≤ 2 ^ width) :
    (NormalizedVector.ket (R := Qubits padding) 0).tensor
        (uniformState N width hN hfits) =
      uniformState N (padding + width) hN
        (fits_pad hfits (Nat.le_add_left width padding)) := by
  apply NormalizedVector.ext
  intro index
  rcases (prodEquiv (m := padding) (n := width)).surjective index with
    ⟨⟨high, low⟩, rfl⟩
  rw [NormalizedVector.tensor_apply_prod,
    uniformState_apply, uniformState_apply]
  by_cases hhigh : high = 0
  · subst high
    simp [NormalizedVector.ket_apply, prodEquiv, finProdFinEquiv]
  · have hval : high.val ≠ 0 := by
      intro hzero
      apply hhigh
      exact Fin.ext hzero
    have hpositive : 1 ≤ high.val := Nat.one_le_iff_ne_zero.mpr hval
    have hpowle : 2 ^ width ≤ 2 ^ width * high.val := by
      simpa using Nat.mul_le_mul_left (2 ^ width) hpositive
    have hbelow : N ≤ (prodEquiv (m := padding) (n := width) (high, low)).val := by
      change N ≤ low.val + 2 ^ width * high.val
      exact hfits.trans (by omega)
    simp [NormalizedVector.ket_apply, hhigh, Nat.not_lt_of_ge hbelow]

/-- High-zero padding of a literal circuit by an identity tensor. -/
def padHigh {source target : Nat} (hwidth : source ≤ target)
    (program : UnitaryCircuit (Qubits source)) : UnitaryCircuit (Qubits target) :=
  castWidth (Nat.sub_add_cancel hwidth)
    (UnitaryCircuit.prodRight (m := target - source) program)

@[simp]
theorem padHigh_eventTrace {source target : Nat} (hwidth : source ≤ target)
    (program : UnitaryCircuit (Qubits source)) :
    (padHigh hwidth program).eventTrace = program.eventTrace := by
  simp [padHigh]

@[simp]
theorem padHigh_eventCost {source target : Nat} (hwidth : source ≤ target)
    (program : UnitaryCircuit (Qubits source)) :
    (padHigh hwidth program).eventCost = program.eventCost := by
  simp [padHigh]

@[simp]
theorem padHigh_evaluatedEventDepth {source target : Nat}
    (hwidth : source ≤ target) (program : UnitaryCircuit (Qubits source))
    (assign : Resource.Event .quantum → Nat) :
    (padHigh hwidth program).evaluatedEventDepth assign =
      program.evaluatedEventDepth assign := by
  simp [padHigh]

/-- The explicit all-zero input factors across a high-zero padding split. -/
theorem ket_zero_split {padding width : Nat} :
    NormalizedVector.ket (R := Qubits (padding + width)) 0 =
      (NormalizedVector.ket (R := Qubits padding) 0).tensor
        (NormalizedVector.ket (R := Qubits width) 0) := by
  rw [NormalizedVector.tensor_ket]
  congr 1

/-- Equality transport does not change the explicit range-uniform vector. -/
theorem castWidthState_uniformState {N source target : Nat}
    (hwidth : source = target) (hN : 0 < N)
    (hsource : N ≤ 2 ^ source) (htarget : N ≤ 2 ^ target) :
    castWidthState hwidth (uniformState N source hN hsource) =
      uniformState N target hN htarget := by
  subst target
  rfl

/-- Padding preserves the actual circuit's zero-input preparation theorem;
the hypothesis is a theorem about the same literal input circuit, not a field
of a resource certificate. -/
theorem padHigh_apply_zero {N source target : Nat} (hN : 0 < N)
    (hfits : N ≤ 2 ^ source) (hwidth : source ≤ target)
    (program : UnitaryCircuit (Qubits source))
    (hprogram : program.applyNormalized
      (NormalizedVector.ket (R := Qubits source) 0) =
        uniformState N source hN hfits) :
    (padHigh hwidth program).applyNormalized
        (NormalizedVector.ket (R := Qubits target) 0) =
      uniformState N target hN (fits_pad hfits hwidth) := by
  unfold padHigh
  rw [← castWidthState_ket_zero (Nat.sub_add_cancel hwidth),
    castWidth_applyNormalized]
  rw [ket_zero_split, prodRight_applyNormalized_tensor, hprogram,
    ket0_tensor_uniformState_pad]
  exact castWidthState_uniformState (Nat.sub_add_cancel hwidth) hN
    (fits_pad hfits (Nat.le_add_left source (target - source)))
    (fits_pad hfits hwidth)

namespace BinaryExpansion

variable {N : Nat}

/-- The actual physical wire carrying source bit `ell j`. -/
def wire (b : BinaryExpansion N) (j : Fin (b.s + 1)) : Fin b.width :=
  WireAddress.littleEndianWire
    ⟨b.ell j, by
      unfold width last
      have hle : b.ell j ≤ b.ell (Fin.last b.s) :=
        b.ell_strict.monotone (Fin.le_last j)
      omega⟩

/-- The physical address of a source bit has precisely the source bit index. -/
theorem bitIndex_wire (b : BinaryExpansion N) (j : Fin (b.s + 1)) :
    (WireAddress.bitIndex (b.wire j)).val = b.ell j := by
  exact congrArg Fin.val (WireAddress.bitIndex_littleEndianWire _)

/-- Consecutive source set-bit positions reverse their physical order. -/
theorem wire_succ_lt_wire (b : BinaryExpansion N) (j : Fin b.s) :
    (b.wire j.succ).val < (b.wire j.castSucc).val := by
  have hell : b.ell j.castSucc < b.ell j.succ :=
    b.ell_strict j.castSucc_lt_succ
  have hsucc_le : b.ell j.succ ≤ b.ell (Fin.last b.s) :=
    b.ell_strict.monotone (Fin.le_last j.succ)
  unfold wire WireAddress.littleEndianWire WireAddress.bitIndex
  dsimp
  unfold width last
  omega

end BinaryExpansion

/-- A literal addressed Hadamard. -/
def hadamardAtWire {width : Nat} (wire : Fin width) : UnitaryCircuit (Qubits width) :=
  atWire wire H

/-- A literal addressed Y-rotation. -/
def rotYAtWire {width : Nat} (wire : Fin width) (θ : ℝ) :
    UnitaryCircuit (Qubits width) :=
  atWire wire (rotY θ)

/-- A literal addressed Pauli-X from the Components primitive family. -/
def xAtWire {width : Nat} (wire : Fin width) : UnitaryCircuit (Qubits width) :=
  QubitPrimitive.circuit (.x wire)

/-- A literal addressed CNOT from the Components primitive family. -/
def cnotAtWire {width : Nat} (control target : Fin width) (hct : control ≠ target) :
    UnitaryCircuit (Qubits width) :=
  QubitPrimitive.circuit (.cnot control target hct)

@[simp]
theorem hadamardAtWire_physical_idx_subset_range {width : Nat} (wire : Fin width) :
    (hadamardAtWire wire).physical_idx ⊆ List.range width := by
  apply atWire_physical_idx_subset_range
  simp [H_system_idx]

@[simp]
theorem rotYAtWire_physical_idx_subset_range {width : Nat} (wire : Fin width)
    (θ : ℝ) :
    (rotYAtWire wire θ).physical_idx ⊆ List.range width := by
  apply atWire_physical_idx_subset_range
  change [0] ⊆ List.range 1
  simp

@[simp]
theorem xAtWire_physical_idx_subset_range {width : Nat} (wire : Fin width) :
    (xAtWire wire).physical_idx ⊆ List.range width := by
  simpa [xAtWire] using (QubitPrimitive.systemIdx_subset_range (.x wire))

@[simp]
theorem cnotAtWire_physical_idx_subset_range {width : Nat}
    (control target : Fin width) (hct : control ≠ target) :
    (cnotAtWire control target hct).physical_idx ⊆ List.range width := by
  simpa [cnotAtWire] using
    (QubitPrimitive.systemIdx_subset_range (.cnot control target hct))

/-- The literal Hadamard coordinate emitted by the schedule. -/
def hadamardEvent : Resource.Event .quantum := .gate (.builtin "hadamard")

/-- The literal Pauli-X coordinate emitted by the schedule. -/
def xEvent : Resource.Event .quantum := .gate (.builtin "x")

/-- The literal CNOT coordinate used by the elementary schedule. -/
def cnotEvent : Resource.Event .quantum := .gate (.builtin "cnot")

/-- The rotation coordinate is independent of the numerical angle.  This is
the strict resource coordinate emitted by every literal `R_Y` leaf. -/
def rotationYEvent : Resource.Event .quantum := (rotYLeaf 0).event

@[simp]
theorem hadamardEvent_eq_gate :
    hadamardEvent = (.gate (.builtin "hadamard") : Resource.Event .quantum) :=
  rfl

@[simp]
theorem xEvent_eq_gate :
    xEvent = (.gate (.builtin "x") : Resource.Event .quantum) :=
  rfl

@[simp]
theorem cnotEvent_eq_gate :
    cnotEvent = (.gate (.builtin "cnot") : Resource.Event .quantum) :=
  rfl

@[simp]
theorem rotationYEvent_eq_gate :
    rotationYEvent =
      (.gate (.declared "QuantumAlg.Components.Gate" "rotation-y") :
        Resource.Event .quantum) :=
  rfl

@[simp]
private theorem atomicEvent_eq_gate (label : Resource.GateLabel) :
    Gate.atomicEvent label = (.gate label : Resource.Event .quantum) :=
  rfl

@[simp]
private theorem walshHadamardEvent_eq_gate :
    WalshHadamard.hadamardEvent = hadamardEvent :=
  rfl

/-- Real gate coordinates permitted by the elementary preparation schedule. -/
def elementaryEvent (event : Resource.Event .quantum) : Prop :=
  event = hadamardEvent ∨ event = xEvent ∨
    event = rotationYEvent ∨ event = cnotEvent

/-- Whether an event is one of the schedule's one-qubit gates. -/
def singleQubitEvent : Resource.Event .quantum → Bool
  | .gate (.builtin "hadamard") => true
  | .gate (.builtin "x") => true
  | .gate (.declared "QuantumAlg.Components.Gate" "rotation-y") => true
  | _ => false

/-- Count the three elementary one-qubit coordinates in the event pool of a
literal circuit.  This is deliberately a projection of `eventCost`, which is
itself derived from the circuit tree, rather than a number supplied beside the
circuit. -/
def singleQubitCost {width : Nat} (program : UnitaryCircuit (Qubits width)) : Nat :=
  ResourcePool.count (.gate (.builtin "hadamard")) program.eventCost +
    ResourcePool.count (.gate (.builtin "x")) program.eventCost +
      ResourcePool.count rotationYEvent program.eventCost

/-- Count the literal CNOT coordinate in the event pool of a circuit. -/
def cnotCost {width : Nat} (program : UnitaryCircuit (Qubits width)) : Nat :=
  ResourcePool.count cnotEvent program.eventCost

/-! ### Elementary two-qubit lowerings

The source schedule is active on zero.  These definitions expose that control
as ordinary `X` gates around a control-on-one CNOT decomposition, so the
stored trace contains only elementary coordinates rather than a controlled
subroutine coordinate. -/

/-- A Y-rotation on the target (physical qubit one) of a two-qubit block. -/
def targetRotY (θ : ℝ) : UnitaryCircuit (Qubits 2) := by
  let control : UnitaryCircuit (Qubits 1) := UnitaryCircuit.identity (Qubits 1) [0] (by simp)
  let target : UnitaryCircuit (Qubits 1) := UnitaryCircuit.shiftPhysicalIdx 1 (rotY θ)
  let layout : PhysicalLayout.DisjointMerge control.physical_idx target.physical_idx :=
    { left_nodup := control.physical_idx_nodup
      right_nodup := target.physical_idx_nodup
      disjoint := by
        change [0].Disjoint [1]
        simp }
  exact UnitaryCircuit.tensorQubits control target layout

/-- A Pauli-X on the control (physical qubit zero) of a two-qubit block. -/
def controlX : UnitaryCircuit (Qubits 2) := by
  let target : UnitaryCircuit (Qubits 1) := UnitaryCircuit.identity (Qubits 1) [1] (by simp)
  let layout : PhysicalLayout.DisjointMerge X.physical_idx target.physical_idx :=
    { left_nodup := X.physical_idx_nodup
      right_nodup := target.physical_idx_nodup
      disjoint := by
        change [0].Disjoint [1]
        simp }
  exact UnitaryCircuit.tensorQubits X target layout

/-- A control-wire X and a target-wire Y-rotation in one physical layer. -/
def controlXParallelTargetRotY (θ : ℝ) : UnitaryCircuit (Qubits 2) := by
  let target : UnitaryCircuit (Qubits 1) := UnitaryCircuit.shiftPhysicalIdx 1 (rotY θ)
  let layout : PhysicalLayout.DisjointMerge X.physical_idx target.physical_idx :=
    { left_nodup := X.physical_idx_nodup
      right_nodup := target.physical_idx_nodup
      disjoint := by
        change [0].Disjoint [1]
        simp }
  exact UnitaryCircuit.tensorQubits X target layout

/-- A CNOT decomposition of a control-on-one `R_Y(theta)`.

The execution order is `R_Y(theta/2)`, CNOT, `R_Y(-theta/2)`, CNOT. -/
def controlledRotY (θ : ℝ) : UnitaryCircuit (Qubits 2) :=
  UnitaryCircuit.seq (targetRotY (θ / 2))
    (UnitaryCircuit.seq CNOT
      (UnitaryCircuit.seq (targetRotY (-(θ / 2))) CNOT))

/-- An active-on-zero `R_Y(theta)`, obtained by conjugating the physical
control wire by X.  Its trace has two CNOTs and four one-qubit gates. -/
def openControlledRotY (θ : ℝ) : UnitaryCircuit (Qubits 2) :=
  UnitaryCircuit.seq (controlXParallelTargetRotY (θ / 2))
    (UnitaryCircuit.seq CNOT
      (UnitaryCircuit.seq (targetRotY (-(θ / 2)))
        (UnitaryCircuit.seq CNOT controlX)))

/-- A CNOT decomposition of a control-on-one Hadamard.

The identity `H = R_Y(-pi/4) X R_Y(pi/4)` makes the execution order
`R_Y(pi/4)`, CNOT, `R_Y(-pi/4)` sufficient. -/
def controlledH : UnitaryCircuit (Qubits 2) :=
  UnitaryCircuit.seq (targetRotY (Real.pi / 4))
    (UnitaryCircuit.seq CNOT (targetRotY (-(Real.pi / 4))) )

/-- An active-on-zero Hadamard using one CNOT and four one-qubit gates. -/
def openControlledH : UnitaryCircuit (Qubits 2) :=
  UnitaryCircuit.seq (controlXParallelTargetRotY (Real.pi / 4))
    (UnitaryCircuit.seq CNOT (controlXParallelTargetRotY (-(Real.pi / 4))))

/-- The target-first counterpart of `targetRotY`: the Y-rotation is on the
left physical wire, so an open control on the right physical wire can be
inserted at the source's (little-endian) positions without a wire swap. -/
def targetFirstRotY (θ : ℝ) : UnitaryCircuit (Qubits 2) :=
  UnitaryCircuit.prodLeft (n := 1) (rotY θ)

/-- A Pauli-X on the right physical wire of a two-qubit block. -/
def rightControlX : UnitaryCircuit (Qubits 2) :=
  UnitaryCircuit.prodRight (m := 1) X

/-- One physical layer containing a target rotation on the left wire and an
X on the right control wire. -/
def targetRotYParallelRightControlX (θ : ℝ) : UnitaryCircuit (Qubits 2) := by
  let control : UnitaryCircuit (Qubits 1) := UnitaryCircuit.shiftPhysicalIdx 1 X
  let layout : PhysicalLayout.DisjointMerge (rotY θ).physical_idx
      control.physical_idx :=
    { left_nodup := (rotY θ).physical_idx_nodup
      right_nodup := control.physical_idx_nodup
      disjoint := by
        change [0].Disjoint [1]
        simp }
  exact UnitaryCircuit.tensorQubits (rotY θ) control layout

/-- The literal addressed CNOT whose control is the right physical wire and
whose target is the left physical wire. -/
def rightControlledCNOT : UnitaryCircuit (Qubits 2) :=
  QubitPrimitive.circuit (.cnot (1 : Fin 2) 0 (by omega))

/-- An active-on-zero Y-rotation with target on the left and control on the
right.  This is the orientation required after converting Algorithm 1's
little-endian source positions to Core's big-endian physical wires. -/
def openControlledRotYRightControl (θ : ℝ) : UnitaryCircuit (Qubits 2) :=
  UnitaryCircuit.seq (targetRotYParallelRightControlX (θ / 2))
    (UnitaryCircuit.seq rightControlledCNOT
      (UnitaryCircuit.seq (targetFirstRotY (-(θ / 2)))
        (UnitaryCircuit.seq rightControlledCNOT rightControlX)))

/-- The basis reindexing that exchanges the two physical qubits of a
two-qubit register.  It is used only to state the mathematical operator of
the right-control lowering; the circuit itself contains the addressed CNOT
and no swap event. -/
def swapQubitIndex : Fin (2 ^ 2) ≃ Fin (2 ^ 2) :=
  swapRegistersPerm 1

/-- A zero-controlled one-qubit operator whose target is physically left and
whose control is physically right. -/
def rightControlledQubitsOnZero (U : UnitaryOperator (Qubits 1)) :
    UnitaryOperator (Qubits 2) :=
  UnitaryOperator.reindex swapQubitIndex
    (UnitaryOperator.controlledQubitsOnZero U)

/-- The explicit two-qubit swap reindex exchanges arbitrary raw tensor
factors.  It is a coordinate identity only; the lowering itself still uses
the addressed CNOT circuit above. -/
theorem reindexVec_swapQubitIndex_tensor
    (left right : HilbertVector (Qubits 1)) :
    reindexVec swapQubitIndex (HilbertVector.tensor left right) =
      HilbertVector.tensor right left := by
  apply WithLp.ofLp_injective
  funext index
  rcases (prodEquiv (m := 1) (n := 1)).surjective index with
    ⟨⟨leftIndex, rightIndex⟩, rfl⟩
  simp [reindexVec_apply, swapQubitIndex, swapRegistersPerm,
    HilbertVector.tensor_apply]
  ring

/-- On a physical `target ⊗ |0⟩` branch, the right-control operator applies
its one-qubit target unitary. -/
theorem rightControlledQubitsOnZero_applyVec_tensor_ket0
    (U : UnitaryOperator (Qubits 1)) (target : HilbertVector (Qubits 1)) :
    (rightControlledQubitsOnZero U).applyVec
        (HilbertVector.tensor target (ket0 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (U.applyVec target)
        (ket0 : HilbertVector (Qubits 1)) := by
  rw [← reindexVec_swapQubitIndex_tensor (ket0 : HilbertVector (Qubits 1)) target]
  unfold rightControlledQubitsOnZero
  rw [unitary_reindex_applyVec,
    UnitaryOperator.controlledQubitsOnZero_applyVec_ket0_tensor,
    reindexVec_swapQubitIndex_tensor]

/-- On a physical `target ⊗ |1⟩` branch, the right-control operator is the
identity. -/
theorem rightControlledQubitsOnZero_applyVec_tensor_ket1
    (U : UnitaryOperator (Qubits 1)) (target : HilbertVector (Qubits 1)) :
    (rightControlledQubitsOnZero U).applyVec
        (HilbertVector.tensor target (ket1 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor target (ket1 : HilbertVector (Qubits 1)) := by
  rw [← reindexVec_swapQubitIndex_tensor (ket1 : HilbertVector (Qubits 1)) target]
  unfold rightControlledQubitsOnZero
  rw [unitary_reindex_applyVec,
    UnitaryOperator.controlledQubitsOnZero_applyVec_ket1_tensor,
    reindexVec_swapQubitIndex_tensor]

/-! The following footprint facts are intentionally proved from the same
literal tensor and sequence constructors as the lowerings.  They are used to
place the complete Algorithm-1 schedule in its full-register interface. -/

private theorem rotY_physical_idx_subset_range_one (θ : ℝ) :
    (rotY θ).physical_idx ⊆ List.range 1 := by
  change [0] ⊆ List.range 1
  simp

private theorem X_physical_idx_subset_range_one :
    X.physical_idx ⊆ List.range 1 := by
  change [0] ⊆ List.range 1
  simp

private theorem CNOT_physical_idx_subset_range_two :
    CNOT.physical_idx ⊆ List.range 2 := by
  change [0, 1] ⊆ List.range 2
  simp

private theorem range_one_subset_range_two : List.range 1 ⊆ List.range 2 := by
  intro index hindex
  simp_all

theorem targetRotY_physical_idx_subset_range (θ : ℝ) :
    (targetRotY θ).physical_idx ⊆ List.range 2 := by
  unfold targetRotY
  dsimp
  apply UnitaryCircuit.tensorQubits_physical_idx_subset
  · simp [UnitaryCircuit.identity]
  · simpa using
      (UnitaryCircuit.shiftPhysicalIdx_physical_idx_subset_range 1 (rotY θ)
        (rotY_physical_idx_subset_range_one θ))

theorem controlX_physical_idx_subset_range :
    controlX.physical_idx ⊆ List.range 2 := by
  unfold controlX
  dsimp
  apply UnitaryCircuit.tensorQubits_physical_idx_subset
  · intro index member
    exact range_one_subset_range_two (X_physical_idx_subset_range_one member)
  · simp [UnitaryCircuit.identity]

theorem controlXParallelTargetRotY_physical_idx_subset_range (θ : ℝ) :
    (controlXParallelTargetRotY θ).physical_idx ⊆ List.range 2 := by
  unfold controlXParallelTargetRotY
  dsimp
  apply UnitaryCircuit.tensorQubits_physical_idx_subset
  · intro index member
    exact range_one_subset_range_two (X_physical_idx_subset_range_one member)
  · simpa using
      (UnitaryCircuit.shiftPhysicalIdx_physical_idx_subset_range 1 (rotY θ)
        (rotY_physical_idx_subset_range_one θ))

theorem targetFirstRotY_physical_idx_subset_range (θ : ℝ) :
    (targetFirstRotY θ).physical_idx ⊆ List.range 2 := by
  unfold targetFirstRotY
  simpa using UnitaryCircuit.prodLeft_physical_idx_subset_range (rotY θ)
    (rotY_physical_idx_subset_range_one θ)

theorem rightControlX_physical_idx_subset_range :
    rightControlX.physical_idx ⊆ List.range 2 := by
  unfold rightControlX
  simpa using UnitaryCircuit.prodRight_physical_idx_subset_range X
    X_physical_idx_subset_range_one

theorem targetRotYParallelRightControlX_physical_idx_subset_range (θ : ℝ) :
    (targetRotYParallelRightControlX θ).physical_idx ⊆ List.range 2 := by
  unfold targetRotYParallelRightControlX
  dsimp
  apply UnitaryCircuit.tensorQubits_physical_idx_subset
  · intro index member
    exact range_one_subset_range_two
      (rotY_physical_idx_subset_range_one θ member)
  · simpa using
      (UnitaryCircuit.shiftPhysicalIdx_physical_idx_subset_range 1 X
        X_physical_idx_subset_range_one)

theorem rightControlledCNOT_physical_idx_subset_range :
    rightControlledCNOT.physical_idx ⊆ List.range 2 := by
  simpa [rightControlledCNOT] using
    (QubitPrimitive.systemIdx_subset_range
      (.cnot (1 : Fin 2) 0 (by omega)))

theorem openControlledH_physical_idx_subset_range :
    openControlledH.physical_idx ⊆ List.range 2 := by
  unfold openControlledH
  apply UnitaryCircuit.seq_physical_idx_subset
  · exact controlXParallelTargetRotY_physical_idx_subset_range _
  · apply UnitaryCircuit.seq_physical_idx_subset
    · exact CNOT_physical_idx_subset_range_two
    · exact controlXParallelTargetRotY_physical_idx_subset_range _

theorem openControlledRotYRightControl_physical_idx_subset_range (θ : ℝ) :
    (openControlledRotYRightControl θ).physical_idx ⊆ List.range 2 := by
  unfold openControlledRotYRightControl
  apply UnitaryCircuit.seq_physical_idx_subset
  · exact targetRotYParallelRightControlX_physical_idx_subset_range _
  · apply UnitaryCircuit.seq_physical_idx_subset
    · exact rightControlledCNOT_physical_idx_subset_range
    · apply UnitaryCircuit.seq_physical_idx_subset
      · exact targetFirstRotY_physical_idx_subset_range _
      · apply UnitaryCircuit.seq_physical_idx_subset
        · exact rightControlledCNOT_physical_idx_subset_range
        · exact rightControlX_physical_idx_subset_range

private theorem rotY_eventTrace_base (θ : ℝ) :
    (rotY θ).eventTrace =
      [Resource.Event.gate
        (.declared "QuantumAlg.Components.Gate" "rotation-y")] :=
  rfl

private theorem X_eventTrace_base :
    X.eventTrace = [Resource.Event.gate (.builtin "x")] :=
  rfl

private theorem rightControlledCNOT_eventTrace_base :
    rightControlledCNOT.eventTrace =
      [Resource.Event.gate (.builtin "cnot")] :=
  rfl

@[simp]
theorem targetFirstRotY_eventTrace (θ : ℝ) :
    (targetFirstRotY θ).eventTrace = [(rotYLeaf θ).event] := by
  simp [targetFirstRotY, rotY_eventTrace_base]

@[simp]
theorem rightControlX_eventTrace :
    rightControlX.eventTrace = [Gate.atomicEvent (.builtin "x")] := by
  simp [rightControlX, X_eventTrace_base, Gate.atomicEvent]

@[simp]
theorem targetRotYParallelRightControlX_eventTrace (θ : ℝ) :
    (targetRotYParallelRightControlX θ).eventTrace =
      [(rotYLeaf θ).event, Gate.atomicEvent (.builtin "x")] := by
  simp [targetRotYParallelRightControlX, rotY_eventTrace_base,
    X_eventTrace_base, Gate.atomicEvent]

@[simp]
theorem rightControlledCNOT_eventTrace :
    rightControlledCNOT.eventTrace = [Gate.atomicEvent (.builtin "cnot")] := by
  simpa [Gate.atomicEvent] using rightControlledCNOT_eventTrace_base

@[simp]
theorem openControlledRotYRightControl_eventTrace (θ : ℝ) :
    (openControlledRotYRightControl θ).eventTrace =
      [(rotYLeaf (θ / 2)).event, Gate.atomicEvent (.builtin "x"),
        Gate.atomicEvent (.builtin "cnot"), (rotYLeaf (-(θ / 2))).event,
        Gate.atomicEvent (.builtin "cnot"), Gate.atomicEvent (.builtin "x")] := by
  simp [openControlledRotYRightControl]

/-- Place a two-qubit target/control block on two physical wires with an
untouched middle register.  The `left` wire is physically earlier than the
`right` wire; all widening is by identity tensors. -/
def atSeparatedWires {width : Nat} (left right : Fin width)
    (hleft : left.val < right.val) (program : UnitaryCircuit (Qubits 2)) :
    UnitaryCircuit (Qubits width) :=
  castWidth (by
    omega : left.val + (1 + (right.val - left.val - 1) + 1) +
      (width - right.val - 1) = width)
    (UnitaryCircuit.prodLeft (n := width - right.val - 1)
      (UnitaryCircuit.prodRight (m := left.val)
        (UnitaryCircuit.insertMiddle (leftWidth := 1)
          (middleWidth := right.val - left.val - 1) (rightWidth := 1) program)))

@[simp]
theorem atSeparatedWires_eventTrace {width : Nat} (left right : Fin width)
    (hleft : left.val < right.val) (program : UnitaryCircuit (Qubits 2)) :
    (atSeparatedWires left right hleft program).eventTrace = program.eventTrace := by
  simp [atSeparatedWires]

@[simp]
theorem atSeparatedWires_eventCost {width : Nat} (left right : Fin width)
    (hleft : left.val < right.val) (program : UnitaryCircuit (Qubits 2)) :
    (atSeparatedWires left right hleft program).eventCost = program.eventCost := by
  simp [atSeparatedWires]

@[simp]
theorem atSeparatedWires_evaluatedEventDepth {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (program : UnitaryCircuit (Qubits 2)) (assign : Resource.Event .quantum → Nat) :
    (atSeparatedWires left right hleft program).evaluatedEventDepth assign =
      program.evaluatedEventDepth assign := by
  simp [atSeparatedWires]

/-- Separating two canonically placed physical wires with identity tensors
keeps the literal two-wire program inside the enlarged full-register range. -/
theorem atSeparatedWires_physical_idx_subset_range {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (program : UnitaryCircuit (Qubits 2))
    (contained : program.physical_idx ⊆ List.range 2) :
    (atSeparatedWires left right hleft program).physical_idx ⊆
      List.range width := by
  have inserted :
      (UnitaryCircuit.insertMiddle (leftWidth := 1)
        (middleWidth := right.val - left.val - 1) (rightWidth := 1)
        program).physical_idx ⊆
        List.range (1 + (right.val - left.val - 1) + 1) :=
    UnitaryCircuit.insertMiddle_physical_idx_subset_range
      (leftWidth := 1) (middleWidth := right.val - left.val - 1)
      (rightWidth := 1) program contained
  have prefixed :
      (UnitaryCircuit.prodRight (m := left.val)
        (UnitaryCircuit.insertMiddle (leftWidth := 1)
          (middleWidth := right.val - left.val - 1) (rightWidth := 1)
          program)).physical_idx ⊆
        List.range (left.val + (1 + (right.val - left.val - 1) + 1)) :=
    UnitaryCircuit.prodRight_physical_idx_subset_range _ inserted
  have lifted :
      (UnitaryCircuit.prodLeft (n := width - right.val - 1)
        (UnitaryCircuit.prodRight (m := left.val)
          (UnitaryCircuit.insertMiddle (leftWidth := 1)
            (middleWidth := right.val - left.val - 1) (rightWidth := 1)
            program))).physical_idx ⊆
        List.range
          (left.val + (1 + (right.val - left.val - 1) + 1) +
            (width - right.val - 1)) :=
    UnitaryCircuit.prodLeft_physical_idx_subset_range _ prefixed
  rw [atSeparatedWires, castWidth_physical_idx]
  simpa only [show left.val + (1 + (right.val - left.val - 1) + 1) +
      (width - right.val - 1) = width by omega] using lifted

/-- A normalized state split at two physically separated wires.  The middle
register is transported by the same explicit index insertion used by
`atSeparatedWires`; no fictitious swap or free wire reindex is introduced. -/
def atSeparatedState {width : Nat} (left right : Fin width)
    (hleft : left.val < right.val)
    (leading : NormalizedVector (Qubits left.val))
    (body : NormalizedVector (Qubits 2))
    (middle : NormalizedVector (Qubits (right.val - left.val - 1)))
    (suffix : NormalizedVector (Qubits (width - right.val - 1))) :
    NormalizedVector (Qubits width) :=
  castWidthState (by
    omega : left.val + (1 + (right.val - left.val - 1) + 1) +
      (width - right.val - 1) = width)
    ((leading.tensor (insertMiddleState body middle)).tensor suffix)

/-- The separated-wire lifting acts on an arbitrary normalized two-wire
state exactly as its literal two-wire circuit, leaving the other three
registers unchanged. -/
theorem atSeparatedWires_applyNormalized_state {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (program : UnitaryCircuit (Qubits 2))
    (leading : NormalizedVector (Qubits left.val))
    (body : NormalizedVector (Qubits 2))
    (middle : NormalizedVector (Qubits (right.val - left.val - 1)))
    (suffix : NormalizedVector (Qubits (width - right.val - 1))) :
    (atSeparatedWires left right hleft program).applyNormalized
        (atSeparatedState left right hleft leading body middle suffix) =
      atSeparatedState left right hleft leading
        (program.applyNormalized body) middle suffix := by
  unfold atSeparatedWires atSeparatedState
  rw [castWidth_applyNormalized,
    prodLeft_applyNormalized_tensor,
    prodRight_applyNormalized_tensor,
    insertMiddle_applyNormalized_state]

/-- Raw-vector state assembled around two physically separated wires. -/
def atSeparatedVec {width : Nat} (left right : Fin width)
    (hleft : left.val < right.val)
    (leading : HilbertVector (Qubits left.val))
    (body : HilbertVector (Qubits 2))
    (middle : HilbertVector (Qubits (right.val - left.val - 1)))
    (suffix : HilbertVector (Qubits (width - right.val - 1))) :
    HilbertVector (Qubits width) :=
  castWidthVec (by
    omega : left.val + (1 + (right.val - left.val - 1) + 1) +
      (width - right.val - 1) = width)
    ((HilbertVector.tensor leading (insertMiddleVec body middle)).tensor suffix)

/-- Raw-vector action of the separated-wire lifting. -/
theorem atSeparatedWires_applyVec {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (program : UnitaryCircuit (Qubits 2))
    (leading : HilbertVector (Qubits left.val))
    (body : HilbertVector (Qubits 2))
    (middle : HilbertVector (Qubits (right.val - left.val - 1)))
    (suffix : HilbertVector (Qubits (width - right.val - 1))) :
    (atSeparatedWires left right hleft program).applyVec
        (atSeparatedVec left right hleft leading body middle suffix) =
      atSeparatedVec left right hleft leading
        (program.applyVec body) middle suffix := by
  unfold atSeparatedWires atSeparatedVec
  rw [castWidth_applyVec, prodLeft_applyVec_tensor, prodRight_applyVec_tensor,
    insertMiddle_applyVec]

/-- The raw separated-wire assembly is linear in the actual two-wire body.
This is the bridge used to distribute a literal controlled rotation's two
branches before the subsequent literal controlled-H layer is applied. -/
@[simp]
theorem atSeparatedVec_add_body {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (leading : HilbertVector (Qubits left.val))
    (body body' : HilbertVector (Qubits 2))
    (middle : HilbertVector (Qubits (right.val - left.val - 1)))
    (suffix : HilbertVector (Qubits (width - right.val - 1))) :
    atSeparatedVec left right hleft leading (body + body') middle suffix =
      atSeparatedVec left right hleft leading body middle suffix +
        atSeparatedVec left right hleft leading body' middle suffix := by
  unfold atSeparatedVec
  rw [insertMiddleVec_add, HilbertVector.tensor_add,
    HilbertVector.add_tensor, castWidthVec_add]

@[simp]
theorem atSeparatedVec_smul_body {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (leading : HilbertVector (Qubits left.val))
    (scalar : ℂ) (body : HilbertVector (Qubits 2))
    (middle : HilbertVector (Qubits (right.val - left.val - 1)))
    (suffix : HilbertVector (Qubits (width - right.val - 1))) :
    atSeparatedVec left right hleft leading (scalar • body) middle suffix =
      scalar • atSeparatedVec left right hleft leading body middle suffix := by
  unfold atSeparatedVec
  rw [insertMiddleVec_smul, HilbertVector.tensor_smul,
    HilbertVector.smul_tensor, castWidthVec_smul]

/-- When the separated two-wire body is itself a tensor, the concrete
middle insertion exposes the five physical factors in their literal
left-to-right order.  This is a definitional tensor-layout bridge, not a
logical wire permutation. -/
private theorem atSeparatedVec_tensor_body {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (leading : HilbertVector (Qubits left.val))
    (first : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits (right.val - left.val - 1)))
    (second : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits (width - right.val - 1))) :
    atSeparatedVec left right hleft leading
        (HilbertVector.tensor first second) middle suffix =
      castWidthVec (by
        omega : left.val + (1 + (right.val - left.val - 1) + 1) +
          (width - right.val - 1) = width)
        ((HilbertVector.tensor leading
          (HilbertVector.tensor (HilbertVector.tensor first middle) second)).tensor
          suffix) := by
  unfold atSeparatedVec
  rw [insertMiddleVec_tensor]

/-- `atSeparatedVec` with factor widths transported from source arithmetic
reduces to its concrete five-factor tensor.  The width equalities are
eliminated before using `atSeparatedVec_tensor_body`, so this is a genuine
transport lemma rather than a logical wire relabelling. -/
private theorem atSeparatedVec_tensor_body_transport {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    {highWidth middleWidth suffixWidth : Nat}
    (hhigh : highWidth = left.val)
    (hmiddle : middleWidth = right.val - left.val - 1)
    (hsuffix : suffixWidth = width - right.val - 1)
    (high : HilbertVector (Qubits highWidth))
    (first : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits middleWidth))
    (second : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits suffixWidth)) :
    atSeparatedVec left right hleft
        (castWidthVec hhigh high)
        (HilbertVector.tensor first second)
        (castWidthVec hmiddle middle)
        (castWidthVec hsuffix suffix) =
      castWidthVec (by
        omega : (highWidth + ((1 + middleWidth) + 1)) + suffixWidth = width)
        (HilbertVector.tensor
          (HilbertVector.tensor high
            (HilbertVector.tensor (HilbertVector.tensor first middle) second))
          suffix) := by
  subst highWidth
  subst middleWidth
  subst suffixWidth
  simpa only [castWidthVec_self] using
    (atSeparatedVec_tensor_body left right hleft high first middle second suffix)

/-- The concrete product label underlying one separated two-wire basis
configuration.  The two explicit one-qubit fields occur in physical
left-to-right order; callers may consequently use it both for leading-control
and right-control lowerings without reindexing a circuit. -/
private def separatedBasisLabel {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (leading : Fin (2 ^ left.val)) (first : Fin (2 ^ 1))
    (middle : Fin (2 ^ (right.val - left.val - 1)))
    (second : Fin (2 ^ 1))
    (suffix : Fin (2 ^ (width - right.val - 1))) : Fin (2 ^ width) :=
  castWidthIndex (by
    omega : left.val + (1 + (right.val - left.val - 1) + 1) +
      (width - right.val - 1) = width)
    (prodEquiv
      (m := left.val + (1 + (right.val - left.val - 1) + 1))
      (n := width - right.val - 1)
      (prodEquiv
        (m := left.val) (n := 1 + (right.val - left.val - 1) + 1)
        (leading,
          prodEquiv (m := 1 + (right.val - left.val - 1)) (n := 1)
            (prodEquiv (m := 1) (n := right.val - left.val - 1)
              (first, middle), second)), suffix))

/-- A separated raw basis tensor is exactly the computational ket at its
explicit physical product label. -/
private theorem atSeparatedVec_ket {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (leading : Fin (2 ^ left.val)) (first : Fin (2 ^ 1))
    (middle : Fin (2 ^ (right.val - left.val - 1)))
    (second : Fin (2 ^ 1))
    (suffix : Fin (2 ^ (width - right.val - 1))) :
    atSeparatedVec left right hleft
        (basisKetVec leading)
        (basisKetVec (prodEquiv (m := 1) (n := 1) (first, second)))
        (basisKetVec middle) (basisKetVec suffix) =
      basisKetVec
        (separatedBasisLabel left right hleft leading first middle second suffix) := by
  unfold atSeparatedVec insertMiddleVec separatedBasisLabel
  simp only [raw_tensor_ket, reindexVec_ket, castWidthVec_ket]
  simp [UnitaryCircuit.insertMiddleIndexEquiv]

private theorem atSeparatedVec_tensor_ket {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (leading : Fin (2 ^ left.val)) (first : Fin (2 ^ 1))
    (middle : Fin (2 ^ (right.val - left.val - 1)))
    (second : Fin (2 ^ 1))
    (suffix : Fin (2 ^ (width - right.val - 1))) :
    atSeparatedVec left right hleft
        (basisKetVec leading)
        (HilbertVector.tensor (basisKetVec first) (basisKetVec second))
        (basisKetVec middle) (basisKetVec suffix) =
      basisKetVec
        (separatedBasisLabel left right hleft leading first middle second suffix) := by
  rw [raw_tensor_ket, atSeparatedVec_ket]

/-- Splitting the all-zero raw ket at any two distinct physical wires gives
the corresponding all-zero five-field separated vector. -/
private theorem atSeparatedVec_all_ket0 {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val) :
    atSeparatedVec left right hleft
        (rawKetZero left.val)
        (HilbertVector.tensor (rawKetZero 1) (rawKetZero 1))
        (rawKetZero (right.val - left.val - 1))
        (rawKetZero (width - right.val - 1)) =
      rawKetZero width := by
  unfold rawKetZero
  rw [raw_tensor_ket]
  rw [atSeparatedVec_ket]
  congr 1

/-- On a first/last split, the active open-H output has the simple contiguous
form needed by the recursive strip: all unchanged wires precede the newly
created rightmost `|+⟩`. -/
private theorem atSeparatedVec_ket0_ketPlus_last (count : Nat) :
    atSeparatedVec (0 : Fin (count + 2)) (Fin.last (count + 1)) (by simp)
        (rawKetZero 0)
        (HilbertVector.tensor (rawKetZero 1)
          (ketPlus : HilbertVector (Qubits 1)))
        (rawKetZero count)
        (rawKetZero
          (count + 2 - (Fin.last (count + 1)).val - 1)) =
      castWidthVec (by omega : (1 + count) + 1 = count + 2)
        (HilbertVector.tensor
          (rawKetZero (1 + count))
          (ketPlus : HilbertVector (Qubits 1))) := by
  have hlayout := atSeparatedVec_tensor_body_transport
    (left := (0 : Fin (count + 2)))
    (right := Fin.last (count + 1)) (hleft := by simp)
    (hhigh := by simp) (hmiddle := by simp [Fin.val_last])
    (hsuffix := by simp [Fin.val_last])
    (high := rawKetZero 0) (first := rawKetZero 1)
    (middle := rawKetZero count)
    (second := (ketPlus : HilbertVector (Qubits 1)))
    (suffix := rawKetZero 0)
  calc
    _ = castWidthVec (by omega : (0 + ((1 + count) + 1)) + 0 = count + 2)
          (HilbertVector.tensor
            (HilbertVector.tensor (rawKetZero 0)
              (HilbertVector.tensor
                (HilbertVector.tensor (rawKetZero 1) (rawKetZero count))
                (ketPlus : HilbertVector (Qubits 1))))
            (rawKetZero 0)) := by
          simpa [Fin.val_last] using hlayout
    _ = _ := by
          rw [raw_tensor_ket0]
          simpa using
            (castWidthVec_raw_ket0_both_zero
              (by omega : ((1 + count) + 1) = count + 2)
              (HilbertVector.tensor (rawKetZero (1 + count))
                (ketPlus : HilbertVector (Qubits 1))))

/-- The first/last separated layout agrees with the ordinary three-factor
tensor order on computational kets.  This is the basis bridge for the
control-one strip induction. -/
private theorem atSeparatedVec_first_last_ket (count : Nat)
    (first : Fin (2 ^ 1)) (middle : Fin (2 ^ count))
    (second : Fin (2 ^ 1)) :
    atSeparatedVec (0 : Fin (count + 2)) (Fin.last (count + 1)) (by simp)
        (rawKetZero 0)
        (HilbertVector.tensor
          (basisKetVec first) (basisKetVec second))
        (basisKetVec middle)
        (rawKetZero
          (count + 2 - (Fin.last (count + 1)).val - 1)) =
      castWidthVec (by omega : (1 + count) + 1 = count + 2)
        (HilbertVector.tensor
          (HilbertVector.tensor
          (basisKetVec first) (basisKetVec middle))
          (basisKetVec second)) := by
  have hlayout := atSeparatedVec_tensor_body_transport
    (left := (0 : Fin (count + 2)))
    (right := Fin.last (count + 1)) (hleft := by simp)
    (hhigh := by simp) (hmiddle := by simp [Fin.val_last])
    (hsuffix := by simp [Fin.val_last])
    (high := rawKetZero 0) (first := basisKetVec first)
    (middle := basisKetVec middle) (second := basisKetVec second)
    (suffix := rawKetZero 0)
  calc
    _ = castWidthVec (by omega : (0 + ((1 + count) + 1)) + 0 = count + 2)
          (HilbertVector.tensor
            (HilbertVector.tensor (rawKetZero 0)
              (HilbertVector.tensor
                (HilbertVector.tensor (basisKetVec first) (basisKetVec middle))
                (basisKetVec second)))
            (rawKetZero 0)) := by
          simpa [Fin.val_last] using hlayout
    _ = _ := by
          simpa using
            (castWidthVec_raw_ket0_both_zero
              (by omega : ((1 + count) + 1) = count + 2)
              (HilbertVector.tensor
                (HilbertVector.tensor (basisKetVec first) (basisKetVec middle))
                (basisKetVec second)))

/-- Reading the first explicit one-qubit field of a separated label is the
physical bit read at its left wire.  This is a coordinate lemma, not a wire
permutation: the nested `prodEquiv` terms are precisely the tensors used by
`atSeparatedVec`. -/
private theorem separatedBasisLabel_testBit_first {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (leading : Fin (2 ^ left.val)) (first : Fin (2 ^ 1))
    (middle : Fin (2 ^ (right.val - left.val - 1)))
    (second : Fin (2 ^ 1))
    (suffix : Fin (2 ^ (width - right.val - 1))) :
    (separatedBasisLabel left right hleft leading first middle second suffix).val.testBit
        (WireAddress.bitIndex left).val = first.val.testBit 0 := by
  let firstMiddle : Fin (2 ^ (1 + (right.val - left.val - 1))) :=
    prodEquiv (m := 1) (n := right.val - left.val - 1) (first, middle)
  let inside : Fin (2 ^ (1 + (right.val - left.val - 1) + 1)) :=
    prodEquiv (m := 1 + (right.val - left.val - 1)) (n := 1)
      (firstMiddle, second)
  let head : Fin (2 ^ (left.val + (1 + (right.val - left.val - 1) + 1))) :=
    prodEquiv (m := left.val) (n := 1 + (right.val - left.val - 1) + 1)
      (leading, inside)
  let raw : Fin
      (2 ^ ((left.val + (1 + (right.val - left.val - 1) + 1)) +
        (width - right.val - 1))) :=
    prodEquiv (m := left.val + (1 + (right.val - left.val - 1) + 1))
      (n := width - right.val - 1) (head, suffix)
  have houter := prodEquiv_testBit_left head suffix
    ⟨right.val - left.val, by
      omega⟩
  have hhead := prodEquiv_testBit_right leading inside
    ⟨right.val - left.val, by
      omega⟩
  have hinside := prodEquiv_testBit_left firstMiddle second
    ⟨right.val - left.val - 1, by
      omega⟩
  have hfirst := prodEquiv_testBit_left first middle ⟨0, by omega⟩
  have hfirstIndex : width - 1 - left.val =
      (width - right.val - 1) + (right.val - left.val) := by
    omega
  have hinsideIndex : right.val - left.val =
      1 + (right.val - left.val - 1) := by
    omega
  change (castWidthIndex (by omega :
      (left.val + (1 + (right.val - left.val - 1) + 1)) +
        (width - right.val - 1) = width) raw).val.testBit
        (width - 1 - left.val) = first.val.testBit 0
  simp only [castWidthIndex_val]
  calc
    raw.val.testBit (width - 1 - left.val) =
        head.val.testBit (right.val - left.val) := by
          simpa only [raw, hfirstIndex] using houter
    _ = inside.val.testBit (right.val - left.val) := by
          simpa only [head] using hhead
    _ = inside.val.testBit (1 + (right.val - left.val - 1)) := by
          exact congrArg (fun bit => inside.val.testBit bit) hinsideIndex
    _ = firstMiddle.val.testBit (right.val - left.val - 1) := by
          simpa only [inside] using hinside
    _ = first.val.testBit 0 := by
          simpa only [firstMiddle, Nat.add_zero] using hfirst

/-- Reading the second explicit one-qubit field of a separated label is the
physical bit read at its right wire. -/
private theorem separatedBasisLabel_testBit_second {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (leading : Fin (2 ^ left.val)) (first : Fin (2 ^ 1))
    (middle : Fin (2 ^ (right.val - left.val - 1)))
    (second : Fin (2 ^ 1))
    (suffix : Fin (2 ^ (width - right.val - 1))) :
    (separatedBasisLabel left right hleft leading first middle second suffix).val.testBit
        (WireAddress.bitIndex right).val = second.val.testBit 0 := by
  let firstMiddle : Fin (2 ^ (1 + (right.val - left.val - 1))) :=
    prodEquiv (m := 1) (n := right.val - left.val - 1) (first, middle)
  let inside : Fin (2 ^ (1 + (right.val - left.val - 1) + 1)) :=
    prodEquiv (m := 1 + (right.val - left.val - 1)) (n := 1)
      (firstMiddle, second)
  let head : Fin (2 ^ (left.val + (1 + (right.val - left.val - 1) + 1))) :=
    prodEquiv (m := left.val) (n := 1 + (right.val - left.val - 1) + 1)
      (leading, inside)
  let raw : Fin
      (2 ^ ((left.val + (1 + (right.val - left.val - 1) + 1)) +
        (width - right.val - 1))) :=
    prodEquiv (m := left.val + (1 + (right.val - left.val - 1) + 1))
      (n := width - right.val - 1) (head, suffix)
  have houter := prodEquiv_testBit_left head suffix ⟨0, by
    omega⟩
  have hhead := prodEquiv_testBit_right leading inside ⟨0, by
    omega⟩
  have hinside := prodEquiv_testBit_right firstMiddle second ⟨0, by omega⟩
  have hsecondIndex : width - 1 - right.val = width - right.val - 1 := by
    omega
  change (castWidthIndex (by omega :
      (left.val + (1 + (right.val - left.val - 1) + 1)) +
        (width - right.val - 1) = width) raw).val.testBit
        (width - 1 - right.val) = second.val.testBit 0
  simp only [castWidthIndex_val]
  calc
    raw.val.testBit (width - 1 - right.val) = head.val.testBit 0 := by
      simpa only [raw, hsecondIndex, Nat.add_zero] using houter
    _ = inside.val.testBit 0 := by
      simpa only [head] using hhead
    _ = second.val.testBit 0 := by
      simpa only [inside] using hinside

/-- Every full-register basis address admits the explicit five-field split
used by `atSeparatedVec`.  This finite decomposition is later used to lift
the inactive-control basis equation to a raw residual block by linearity. -/
private theorem exists_separatedBasisLabel {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (index : Fin (2 ^ width)) :
    ∃ (leading : Fin (2 ^ left.val)) (first : Fin (2 ^ 1))
      (middle : Fin (2 ^ (right.val - left.val - 1)))
      (second : Fin (2 ^ 1))
      (suffix : Fin (2 ^ (width - right.val - 1))),
      separatedBasisLabel left right hleft leading first middle second suffix = index := by
  let sourceWidth := left.val + (1 + (right.val - left.val - 1) + 1) +
    (width - right.val - 1)
  have hwidth : sourceWidth = width := by
    dsimp [sourceWidth]
    omega
  let sourceIndex : Fin (2 ^ sourceWidth) := castWidthIndex hwidth.symm index
  obtain ⟨⟨head, suffix⟩, houter⟩ :=
    (prodEquiv (m := left.val + (1 + (right.val - left.val - 1) + 1))
      (n := width - right.val - 1)).surjective sourceIndex
  obtain ⟨⟨leading, inside⟩, hhead⟩ :=
    (prodEquiv (m := left.val) (n := 1 + (right.val - left.val - 1) + 1)).surjective
      head
  obtain ⟨⟨firstMiddle, second⟩, hinside⟩ :=
    (prodEquiv (m := 1 + (right.val - left.val - 1)) (n := 1)).surjective inside
  obtain ⟨⟨first, middle⟩, hfirstMiddle⟩ :=
    (prodEquiv (m := 1) (n := right.val - left.val - 1)).surjective firstMiddle
  refine ⟨leading, first, middle, second, suffix, ?_⟩
  unfold separatedBasisLabel
  change castWidthIndex hwidth
    (prodEquiv
      (m := left.val + (1 + (right.val - left.val - 1) + 1))
      (n := width - right.val - 1)
      (prodEquiv
        (m := left.val) (n := 1 + (right.val - left.val - 1) + 1)
        (leading,
          prodEquiv (m := 1 + (right.val - left.val - 1)) (n := 1)
            (prodEquiv (m := 1) (n := right.val - left.val - 1)
              (first, middle), second)), suffix)) = index
  rw [hfirstMiddle, hinside, hhead, houter]
  exact castWidthIndex_symm hwidth index

/-- An Algorithm-1 open-controlled rotation at source-mapped physical wires.
The target is physically left of its control. -/
def openControlledRotYAt {width : Nat} (target control : Fin width)
    (htc : target.val < control.val) (θ : ℝ) : UnitaryCircuit (Qubits width) :=
  atSeparatedWires target control htc (openControlledRotYRightControl θ)

/-- An Algorithm-1 open-controlled Hadamard at source-mapped physical wires.
Its high-endpoint control is physically left of the gap target. -/
def openControlledHAt {width : Nat} (control target : Fin width)
    (hct : control.val < target.val) : UnitaryCircuit (Qubits width) :=
  atSeparatedWires control target hct openControlledH

@[simp]
theorem openControlledRotYAt_eventTrace {width : Nat}
    (target control : Fin width) (htc : target.val < control.val) (θ : ℝ) :
    (openControlledRotYAt target control htc θ).eventTrace =
      (openControlledRotYRightControl θ).eventTrace := by
  simp [openControlledRotYAt]

@[simp]
theorem openControlledRotYAt_evaluatedEventDepth {width : Nat}
    (target control : Fin width) (htc : target.val < control.val) (θ : ℝ)
    (assign : Resource.Event .quantum → Nat) :
    (openControlledRotYAt target control htc θ).evaluatedEventDepth assign =
      (openControlledRotYRightControl θ).evaluatedEventDepth assign := by
  simp [openControlledRotYAt]

@[simp]
theorem openControlledHAt_eventTrace {width : Nat}
    (control target : Fin width) (hct : control.val < target.val) :
    (openControlledHAt control target hct).eventTrace = openControlledH.eventTrace := by
  simp [openControlledHAt]

@[simp]
theorem openControlledHAt_evaluatedEventDepth {width : Nat}
    (control target : Fin width) (hct : control.val < target.val)
    (assign : Resource.Event .quantum → Nat) :
    (openControlledHAt control target hct).evaluatedEventDepth assign =
      openControlledH.evaluatedEventDepth assign := by
  simp [openControlledHAt]

theorem openControlledRotYAt_physical_idx_subset_range {width : Nat}
    (target control : Fin width) (htc : target.val < control.val) (θ : ℝ) :
    (openControlledRotYAt target control htc θ).physical_idx ⊆
      List.range width := by
  simpa [openControlledRotYAt] using
    (atSeparatedWires_physical_idx_subset_range target control htc
      (openControlledRotYRightControl θ)
      (openControlledRotYRightControl_physical_idx_subset_range θ))

theorem openControlledHAt_physical_idx_subset_range {width : Nat}
    (control target : Fin width) (hct : control.val < target.val) :
    (openControlledHAt control target hct).physical_idx ⊆ List.range width := by
  simpa [openControlledHAt] using
    (atSeparatedWires_physical_idx_subset_range control target hct
      openControlledH openControlledH_physical_idx_subset_range)

/-! ### Algorithm 1 schedule

The following is the literal Algorithm-1 schedule
[SV24, Uniform.tex:640-664,666-762].  `gap` indexes the transition
from `ell gap` to `ell (gap + 1)`.  The first transition contains the
uncontrolled initial rotation; subsequent transitions contain an open-
controlled rotation.  Every controlled operation is one of the decomposed
circuits above, so the scheduled object has no controlled-event leaf. -/

namespace BinaryExpansion

variable {N : Nat}

/-- A raw computational-basis vector whose address is supplied as a natural
number.  Unlike `NormalizedVector.ket`, this deliberately does not require a
separate bounded subtype witness: the residual-block induction first reasons
about support intervals and obtains the relevant bounds from the binary
expansion itself. -/
def rawKet {width : Nat} (address : Nat) : HilbertVector (Qubits width) :=
  WithLp.toLp 2 fun index => if index.val = address then 1 else 0

@[simp]
theorem rawKet_apply {width : Nat} (address : Nat) (index : Fin (2 ^ width)) :
    rawKet (width := width) address index = if index.val = address then 1 else 0 :=
  rfl

/-- The binary mass strictly above source position `m`.  This is the aligned
base address of the `m`th normalized residual block: all of its lower
`ell m` bits are free, while the set bits above `ell m` remain fixed. -/
def tailMass (b : BinaryExpansion N) (m : Fin (b.s + 1)) : Nat :=
  ∑ j : Fin (b.s + 1),
    if m.val < j.val then 2 ^ b.ell j else 0

/-- The normalized aligned source block occupying
`[tailMass m, tailMass m + 2^(ell m))`.  It is kept as a raw vector because
the Algorithm-1 stage equation is a linear decomposition into mutually
orthogonal blocks, not a decomposition into normalized states. -/
def residualBlock (b : BinaryExpansion N) (m : Fin (b.s + 1)) :
    HilbertVector (Qubits b.width) :=
  WithLp.toLp 2 fun index =>
    if b.tailMass m ≤ index.val ∧
        index.val < b.tailMass m + 2 ^ b.ell m then
      WalshHadamard.invSqrtCard (b.ell m)
    else 0

/-- Pointwise support predicate for one aligned residual block. -/
def residualSupport (b : BinaryExpansion N) (m : Fin (b.s + 1))
    (index : Nat) : Prop :=
  b.tailMass m ≤ index ∧ index < b.tailMass m + 2 ^ b.ell m

@[simp]
theorem residualBlock_apply (b : BinaryExpansion N) (m : Fin (b.s + 1))
    (index : Fin (2 ^ b.width)) :
    b.residualBlock m index =
      if b.tailMass m ≤ index.val ∧
          index.val < b.tailMass m + 2 ^ b.ell m then
        WalshHadamard.invSqrtCard (b.ell m)
      else 0 :=
  rfl

theorem residualBlock_apply_of_not_support (b : BinaryExpansion N)
    (m : Fin (b.s + 1)) (index : Fin (2 ^ b.width))
    (hindex : ¬ b.residualSupport m index.val) :
    b.residualBlock m index = 0 := by
  have hnot : ¬(b.tailMass m ≤ index.val ∧
      index.val < b.tailMass m + 2 ^ b.ell m) := by
    simpa only [residualSupport] using hindex
  rw [residualBlock_apply]
  simp only [if_neg hnot]

/-- The binary mass strictly below an arbitrary source position.  Unlike the
stage-indexed `prefixMass`, this includes the terminal position and is the
natural index for the residual-block induction. -/
def lowerMass (b : BinaryExpansion N) (m : Fin (b.s + 1)) : Nat :=
  ∑ j : Fin (b.s + 1),
    if j.val < m.val then 2 ^ b.ell j else 0

@[simp]
theorem lowerMass_zero (b : BinaryExpansion N) : b.lowerMass 0 = 0 := by
  unfold lowerMass
  simp

/-- Passing one source bit adds exactly that bit's binary mass to the lower
prefix. -/
theorem lowerMass_succ (b : BinaryExpansion N) (m : Fin b.s) :
    b.lowerMass m.succ = b.lowerMass m.castSucc + 2 ^ b.ell m.castSucc := by
  calc
    b.lowerMass m.succ = ∑ index : Fin (b.s + 1),
        ((if index.val < m.castSucc.val then 2 ^ b.ell index else 0) +
          if index = m.castSucc then 2 ^ b.ell index else 0) := by
          unfold lowerMass
          apply Finset.sum_congr rfl
          intro index _
          by_cases hcurrent : index = m.castSucc
          · subst index
            have hbelow : ¬ m.castSucc.val < m.castSucc.val := Nat.lt_irrefl _
            have hsucc : m.val < m.val + 1 := Nat.lt_succ_self m.val
            simp only [Fin.val_castSucc, Fin.val_succ, lt_self_iff_false,
              if_false, if_true, zero_add, hsucc]
          by_cases hbelow : index.val < m.castSucc.val
          · have hbelow' : index.val < m.val := by
              simpa only [Fin.val_castSucc] using hbelow
            have hle : index.val ≤ m.val := Nat.le_of_lt hbelow'
            have hsucc : index.val < m.succ.val := by
              simpa only [Fin.val_succ, Nat.lt_add_one_iff] using hle
            simp only [Fin.val_castSucc, hbelow', if_true, hcurrent,
              if_false, add_zero, hsucc]
          · have hneVal : index.val ≠ m.val := by
              intro hval
              apply hcurrent
              apply Fin.ext
              simpa only [Fin.val_castSucc] using hval
            have hbelow' : ¬ index.val < m.val := by
              simpa only [Fin.val_castSucc] using hbelow
            have hnotle : ¬ index.val ≤ m.val := by omega
            have hsucc : ¬ index.val < m.succ.val := by
              simpa only [Fin.val_succ, Nat.lt_add_one_iff] using hnotle
            simp only [Fin.val_castSucc, hbelow', if_false, hcurrent,
              zero_add, hsucc]
    _ = (∑ index : Fin (b.s + 1),
        if index.val < m.castSucc.val then 2 ^ b.ell index else 0) +
          ∑ index : Fin (b.s + 1),
            if index = m.castSucc then 2 ^ b.ell index else 0 := by
          rw [Finset.sum_add_distrib]
    _ = b.lowerMass m.castSucc + 2 ^ b.ell m.castSucc := by
          simp [lowerMass]

/-- The partial binary mass strictly below the source position `m`. -/
def prefixMass (b : BinaryExpansion N) (m : Fin b.s) : Nat :=
  ∑ j : Fin (b.s + 1),
    if j.val < m.val then 2 ^ b.ell j else 0

@[simp]
theorem lowerMass_castSucc (b : BinaryExpansion N) (m : Fin b.s) :
    b.lowerMass m.castSucc = b.prefixMass m := by
  rfl

/-- Consecutive aligned bases differ by exactly the next binary summand.
Thus the source blocks are adjacent intervals, in decreasing source-index
order. -/
theorem tailMass_eq_pow_add_tailMass_succ (b : BinaryExpansion N)
    (m : Fin b.s) :
    b.tailMass m.castSucc = 2 ^ b.ell m.succ + b.tailMass m.succ := by
  calc
    b.tailMass m.castSucc = ∑ index : Fin (b.s + 1),
        ((if index = m.succ then 2 ^ b.ell index else 0) +
          if m.succ.val < index.val then 2 ^ b.ell index else 0) := by
          unfold tailMass
          apply Finset.sum_congr rfl
          intro index _
          by_cases hnext : index = m.succ
          · subst index
            have hleft : m.val < m.val + 1 := Nat.lt_succ_self m.val
            simp only [Fin.val_castSucc, Fin.val_succ, if_true,
              lt_self_iff_false, if_false, add_zero, hleft]
          by_cases htail : m.succ.val < index.val
          · have htail' : m.val + 1 < index.val := by
              simpa only [Fin.val_succ] using htail
            have hleft : m.castSucc.val < index.val := by
              simpa only [Fin.val_castSucc] using (lt_trans (Nat.lt_succ_self _) htail')
            have hleft' : m.val < index.val := by
              simpa only [Fin.val_castSucc] using hleft
            simp only [Fin.val_castSucc, Fin.val_succ, hnext, if_false,
              hleft', htail', if_true, zero_add]
          · have hleft : ¬ m.castSucc.val < index.val := by
              have htail' : ¬ m.val + 1 < index.val := by
                simpa only [Fin.val_succ] using htail
              have hnextVal : index.val ≠ m.val + 1 := by
                intro hval
                apply hnext
                apply Fin.ext
                simpa only [Fin.val_succ] using hval
              simp only [Fin.val_castSucc]
              omega
            have hleft' : ¬ m.val < index.val := by
              simpa only [Fin.val_castSucc] using hleft
            have htail' : ¬ m.val + 1 < index.val := by
              simpa only [Fin.val_succ] using htail
            simp only [Fin.val_castSucc, Fin.val_succ, hnext, if_false,
              hleft', htail', zero_add]
    _ = (∑ index : Fin (b.s + 1),
        if index = m.succ then 2 ^ b.ell index else 0) +
          ∑ index : Fin (b.s + 1),
            if m.succ.val < index.val then 2 ^ b.ell index else 0 := by
          rw [Finset.sum_add_distrib]
    _ = 2 ^ b.ell m.succ + b.tailMass m.succ := by
          simp [tailMass]

@[simp]
theorem tailMass_last (b : BinaryExpansion N) :
    b.tailMass (Fin.last b.s) = 0 := by
  unfold tailMass
  apply Finset.sum_eq_zero
  intro index _
  have hnot : ¬ (Fin.last b.s).val < index.val := by
    have hle : index.val ≤ b.s := Nat.le_of_lt_succ index.isLt
    simpa only [Fin.val_last, not_lt] using hle
  rw [if_neg hnot]

/-- A residual base together with its own binary summand is bounded by the
whole certified expansion.  This also supplies the range proof for the
literal high-register ket used in the tensor form of a residual block. -/
private theorem tailMass_add_current_le (b : BinaryExpansion N)
    (m : Fin (b.s + 1)) :
    b.tailMass m + 2 ^ b.ell m ≤ N := by
  have hcurrent :
      2 ^ b.ell m = ∑ index : Fin (b.s + 1),
        if index = m then 2 ^ b.ell index else 0 := by
    simp
  rw [hcurrent]
  unfold tailMass
  rw [← Finset.sum_add_distrib]
  calc
    ∑ index : Fin (b.s + 1),
        ((if m.val < index.val then 2 ^ b.ell index else 0) +
          if index = m then 2 ^ b.ell index else 0) ≤
        ∑ index : Fin (b.s + 1), 2 ^ b.ell index := by
      apply Finset.sum_le_sum
      intro index _
      by_cases htail : m.val < index.val
      · have hne : index ≠ m := by
          intro heq
          subst index
          exact (Nat.lt_irrefl m.val) htail
        simp [htail, hne]
      · by_cases hcurrent : index = m
        · subst index
          simp
        · simp [htail, hcurrent]
    _ = N := b.sum_powers.symm

private theorem tailMass_lt_N (b : BinaryExpansion N)
    (m : Fin (b.s + 1)) : b.tailMass m < N := by
  have hbound := b.tailMass_add_current_le m
  have hpositive : 0 < 2 ^ b.ell m := Nat.two_pow_pos _
  omega

private theorem tailMass_lt_pow_width (b : BinaryExpansion N)
    (m : Fin (b.s + 1)) : b.tailMass m < 2 ^ b.width :=
  (b.tailMass_lt_N m).trans_le b.fits_proof

/-- Every summand strictly above `ell m` has the trailing zero bits needed to
make the residual block aligned at its own source position. -/
private theorem pow_succ_ell_dvd_tailMass (b : BinaryExpansion N)
    (m : Fin (b.s + 1)) :
    2 ^ (b.ell m + 1) ∣ b.tailMass m := by
  unfold tailMass
  apply Finset.dvd_sum
  intro index _
  split_ifs with habove
  · apply pow_dvd_pow
    have hstrict : b.ell m < b.ell index :=
      b.ell_strict (by simpa using habove)
    omega
  · exact dvd_zero _

/-- The high prefix of an aligned residual block, after discarding its zero
source bit and all lower free positions. -/
private def residualHigh (b : BinaryExpansion N) (m : Fin (b.s + 1)) : Nat :=
  b.tailMass m / 2 ^ (b.ell m + 1)

private theorem tailMass_eq_residualHigh_mul (b : BinaryExpansion N)
    (m : Fin (b.s + 1)) :
    b.tailMass m = 2 ^ (b.ell m + 1) * b.residualHigh m := by
  unfold residualHigh
  rw [Nat.mul_comm, Nat.div_mul_cancel (b.pow_succ_ell_dvd_tailMass m)]

private theorem ell_lt_width (b : BinaryExpansion N)
    (m : Fin (b.s + 1)) : b.ell m < b.width := by
  unfold width last
  have hle : b.ell m ≤ b.ell (Fin.last b.s) :=
    b.ell_strict.monotone (Fin.le_last m)
  omega

private theorem first_lt_width (b : BinaryExpansion N) : b.first < b.width := by
  unfold first
  exact b.ell_lt_width (0 : Fin (b.s + 1))

private theorem residualHigh_lt (b : BinaryExpansion N)
    (m : Fin (b.s + 1)) :
    b.residualHigh m < 2 ^ (b.width - b.ell m - 1) := by
  have hbit : b.ell m < b.width := b.ell_lt_width m
  have hpow :
      2 ^ b.width =
        2 ^ (b.width - b.ell m - 1) * 2 ^ (b.ell m + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hproduct :
      b.residualHigh m * 2 ^ (b.ell m + 1) <
        2 ^ (b.width - b.ell m - 1) * 2 ^ (b.ell m + 1) := by
    calc
      b.residualHigh m * 2 ^ (b.ell m + 1) = b.tailMass m := by
        unfold residualHigh
        exact Nat.div_mul_cancel (b.pow_succ_ell_dvd_tailMass m)
      _ < 2 ^ b.width := b.tailMass_lt_pow_width m
      _ = 2 ^ (b.width - b.ell m - 1) * 2 ^ (b.ell m + 1) := hpow
  exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mp hproduct

private def residualHighLabel (b : BinaryExpansion N) (m : Fin (b.s + 1)) :
    Fin (2 ^ (b.width - b.ell m - 1)) :=
  ⟨b.residualHigh m, b.residualHigh_lt m⟩

@[simp]
private theorem residualHighLabel_val (b : BinaryExpansion N)
    (m : Fin (b.s + 1)) : (b.residualHighLabel m).val = b.residualHigh m :=
  rfl

/-- The interval support of a residual block is exactly its high fixed prefix,
its own zero source bit, and arbitrary lower coordinates.  This is the
coordinate form that connects the source arithmetic to actual tensor-placed
gates. -/
private theorem residualSupport_iff_tensor_bits (b : BinaryExpansion N)
    (m : Fin (b.s + 1))
    (high : Fin (2 ^ (b.width - b.ell m - 1)))
    (bit : Fin (2 ^ 1)) (low : Fin (2 ^ b.ell m)) :
    b.residualSupport m
        (prodEquiv
          (m := b.width - b.ell m - 1) (n := 1 + b.ell m)
          (high, prodEquiv (m := 1) (n := b.ell m) (bit, low))).val ↔
      high = b.residualHighLabel m ∧ bit = 0 := by
  let q := 2 ^ b.ell m
  let p := 2 ^ (1 + b.ell m)
  let r := b.residualHigh m
  let lower : Fin (2 ^ (1 + b.ell m)) :=
    prodEquiv (m := 1) (n := b.ell m) (bit, low)
  let address : Fin (2 ^ ((b.width - b.ell m - 1) + (1 + b.ell m))) :=
    prodEquiv (m := b.width - b.ell m - 1) (n := 1 + b.ell m)
      (high, lower)
  have hqle : q ≤ p := by
    dsimp [q, p]
    rw [show 1 + b.ell m = b.ell m + 1 by omega, pow_succ]
    omega
  have htail : b.tailMass m = p * r := by
    dsimp [p, r]
    simpa [Nat.add_comm] using b.tailMass_eq_residualHigh_mul m
  have haddress : address.val = lower.val + p * high.val := by
    dsimp [address, p]
    exact prodEquiv_val high lower
  have hlower : lower.val = low.val + q * bit.val := by
    dsimp [lower, q]
    exact prodEquiv_val bit low
  have hquotHigh : address.val / p = high.val := by
    dsimp [address, p]
    simpa only [Equiv.symm_apply_apply] using
      (prodEquiv_symm_fst_val
        (m := b.width - b.ell m - 1) (n := 1 + b.ell m)
        (prodEquiv
          (m := b.width - b.ell m - 1) (n := 1 + b.ell m)
          (high, lower))).symm
  have hquotBit : lower.val / q = bit.val := by
    dsimp [lower, q]
    simpa only [Equiv.symm_apply_apply] using
      (prodEquiv_symm_fst_val (m := 1) (n := b.ell m)
        (prodEquiv (m := 1) (n := b.ell m) (bit, low))).symm
  change b.residualSupport m address.val ↔ _
  constructor
  · rintro ⟨hlo, hhi⟩
    have hdiv : address.val / p = r := by
      apply Nat.div_eq_of_lt_le
      · simpa [htail, Nat.mul_comm] using hlo
      · calc
          address.val < b.tailMass m + q := hhi
          _ ≤ b.tailMass m + p := Nat.add_le_add_left hqle _
          _ = (r + 1) * p := by rw [htail]; ring
    have hhighval : high.val = r := hquotHigh.symm.trans hdiv
    have hhigh : high = b.residualHighLabel m := by
      apply Fin.ext
      simpa [r] using hhighval
    have hlowerlt : lower.val < q := by
      have hrewritten : lower.val + p * r < p * r + q := by
        simpa [haddress, hhighval, htail] using hhi
      omega
    have hbitval : bit.val = 0 := by
      calc
        bit.val = lower.val / q := hquotBit.symm
        _ = 0 := Nat.div_eq_of_lt hlowerlt
    exact ⟨hhigh, Fin.ext hbitval⟩
  · rintro ⟨hhigh, hbit⟩
    subst high
    subst bit
    have haddress' : address.val = b.tailMass m + low.val := by
      calc
        address.val = lower.val + p * (b.residualHighLabel m).val := haddress
        _ = low.val + p * r := by
          rw [hlower]
          simp [residualHighLabel_val, r]
        _ = b.tailMass m + low.val := by rw [htail]; omega
    unfold residualSupport
    constructor
    · rw [haddress']
      omega
    · rw [haddress']
      exact Nat.add_lt_add_left low.isLt _

/-- The raw interval definition of a residual block is equal to its aligned
tensor presentation: a fixed high prefix, a zero source bit, and an actual
low Walsh-uniform block. -/
private theorem residualBlock_tensor_factor (b : BinaryExpansion N)
    (m : Fin (b.s + 1)) :
    b.residualBlock m =
      castWidthVec (by
        have hbit : b.ell m < b.width := b.ell_lt_width m
        omega : (b.width - b.ell m - 1) + (1 + b.ell m) = b.width)
        (HilbertVector.tensor
          (basisKetVec (b.residualHighLabel m))
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
            (WalshHadamard.uniformState (b.ell m) :
              HilbertVector (Qubits (b.ell m))))) := by
  have hbit : b.ell m < b.width := b.ell_lt_width m
  have hwidth : (b.width - b.ell m - 1) + (1 + b.ell m) = b.width := by
    omega
  apply WithLp.ofLp_injective
  funext index
  rw [castWidthVec_apply]
  generalize hsourceIndex : castWidthIndex hwidth.symm index = sourceIndex
  have hindexVal : index.val = sourceIndex.val := by
    rw [← hsourceIndex]
    simp only [castWidthIndex_val]
  rcases (prodEquiv
    (m := b.width - b.ell m - 1) (n := 1 + b.ell m)).surjective sourceIndex with
    ⟨⟨high, lower⟩, rfl⟩
  rcases (prodEquiv (m := 1) (n := b.ell m)).surjective lower with
    ⟨⟨bit, low⟩, rfl⟩
  change (if b.tailMass m ≤ index.val ∧
      index.val < b.tailMass m + 2 ^ b.ell m then
      WalshHadamard.invSqrtCard (b.ell m) else 0) = _
  rw [hindexVal]
  simp only [show
    (b.tailMass m ≤
          (prodEquiv
            (m := b.width - b.ell m - 1) (n := 1 + b.ell m)
            (high, prodEquiv (m := 1) (n := b.ell m) (bit, low))).val ∧
        (prodEquiv
          (m := b.width - b.ell m - 1) (n := 1 + b.ell m)
          (high, prodEquiv (m := 1) (n := b.ell m) (bit, low))).val <
            b.tailMass m + 2 ^ b.ell m) ↔
      high = b.residualHighLabel m ∧ bit = 0 by
        simpa only [residualSupport] using
          b.residualSupport_iff_tensor_bits m high bit low]
  simp only [HilbertVector.tensor_apply_prod]
  by_cases hhigh : high = b.residualHighLabel m
  · subst high
    fin_cases bit <;>
      simp [basisKetVec, ket0, NormalizedVector.ket_apply,
        WalshHadamard.uniformState_apply]
  · simp [basisKetVec, ket0, NormalizedVector.ket_apply, hhigh]

/-- The mass in the strict source interval between two positions.  It is
kept separate from `tailMass` so the proof that an earlier residual block has
a later control bit set can expose the no-carry lower remainder explicitly. -/
private def betweenMass (b : BinaryExpansion N)
    (left right : Fin (b.s + 1)) : Nat :=
  ∑ index : Fin (b.s + 1),
    if left.val < index.val ∧ index.val < right.val then 2 ^ b.ell index else 0

/-- The same interval including its lower endpoint. -/
private def gapLowerMass (b : BinaryExpansion N)
    (left right : Fin (b.s + 1)) : Nat :=
  ∑ index : Fin (b.s + 1),
    if left.val ≤ index.val ∧ index.val < right.val then 2 ^ b.ell index else 0

/-- Any selected finite subfamily of source powers below a strict upper
source exponent has no carry into that exponent. -/
private theorem filtered_powers_lt_pow (b : BinaryExpansion N)
    (predicate : Fin (b.s + 1) → Prop) [DecidablePred predicate]
    (upper : Nat) (hupper : ∀ index, predicate index → b.ell index < upper) :
    (∑ index : Fin (b.s + 1),
      if predicate index then 2 ^ b.ell index else 0) < 2 ^ upper := by
  classical
  rw [← Finset.sum_filter]
  rw [← Finset.sum_image b.ell_strict.injective.injOn]
  exact Nat.geomSum_lt (m := 2)
    (s := (Finset.univ.filter predicate).image b.ell) (n := upper) (by omega)
    (by
      intro exponent hexponent
      rcases Finset.mem_image.mp hexponent with ⟨index, hindex, rfl⟩
      exact hupper index (Finset.mem_filter.mp hindex).2)

/-- The inclusive lower gap mass is still below its upper binary power. -/
private theorem gapLowerMass_lt_pow (b : BinaryExpansion N)
    {left right : Fin (b.s + 1)} (_hleft : left.val < right.val) :
    b.gapLowerMass left right < 2 ^ b.ell right := by
  unfold gapLowerMass
  apply b.filtered_powers_lt_pow
    (fun index => left.val ≤ index.val ∧ index.val < right.val) (b.ell right)
  intro index hindex
  exact b.ell_strict hindex.2

/-- Splitting a tail at a later source position separates the later current
power and the strictly intermediate lower remainder. -/
private theorem tailMass_eq_tailMass_add_current_add_between
    (b : BinaryExpansion N) {left right : Fin (b.s + 1)}
    (hleft : left.val < right.val) :
    b.tailMass left = b.tailMass right + 2 ^ b.ell right +
      b.betweenMass left right := by
  have hcurrent : 2 ^ b.ell right = ∑ index : Fin (b.s + 1),
      if index = right then 2 ^ b.ell index else 0 := by
    simp
  rw [hcurrent]
  unfold tailMass betweenMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  by_cases haboveLeft : left.val < index.val
  · by_cases hbelowRight : index.val < right.val
    · have hnotAboveRight : ¬ right.val < index.val := by omega
      have hnotCurrent : index ≠ right := by
        intro hindex
        subst index
        exact (Nat.lt_irrefl right.val) hbelowRight
      simp [haboveLeft, hbelowRight, hnotAboveRight, hnotCurrent]
    · have hrightLe : right.val ≤ index.val := Nat.le_of_not_gt hbelowRight
      by_cases hcurrentIndex : index = right
      · subst index
        simp [hleft]
      · have haboveRight : right.val < index.val := by
          apply Nat.lt_of_le_of_ne hrightLe
          intro heq
          apply hcurrentIndex
          exact Fin.ext heq.symm
        simp [haboveLeft, hbelowRight, haboveRight, hcurrentIndex]
  · have hnotAboveRight : ¬ right.val < index.val := by omega
    have hnotCurrent : index ≠ right := by
      intro hindex
      subst index
      exact haboveLeft hleft
    simp [haboveLeft, hnotAboveRight, hnotCurrent]

/-- Adding the lower endpoint back to the strict intermediate mass gives the
inclusive gap mass. -/
private theorem gapLowerMass_eq_betweenMass_add_current
    (b : BinaryExpansion N) {left right : Fin (b.s + 1)}
    (hleft : left.val < right.val) :
    b.gapLowerMass left right = b.betweenMass left right + 2 ^ b.ell left := by
  have hcurrent : 2 ^ b.ell left = ∑ index : Fin (b.s + 1),
      if index = left then 2 ^ b.ell index else 0 := by
    simp
  rw [hcurrent]
  unfold gapLowerMass betweenMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  by_cases hcurrentIndex : index = left
  · subst index
    simp [hleft]
  · by_cases hbetween : left.val < index.val ∧ index.val < right.val
    · have hgap : left.val ≤ index.val ∧ index.val < right.val :=
        ⟨Nat.le_of_lt hbetween.1, hbetween.2⟩
      simp [hcurrentIndex, hbetween, hgap]
    · have hnotGap : ¬ (left.val ≤ index.val ∧ index.val < right.val) := by
        intro hgap
        apply hbetween
        constructor
        · exact lt_of_le_of_ne hgap.1 (by
            intro heq
            apply hcurrentIndex
            exact Fin.ext heq.symm)
        · exact hgap.2
      have hnotGapFin : ¬ (left ≤ index ∧ index < right) := by
        intro hgap
        apply hnotGap
        exact ⟨by simpa using hgap.1, by simpa using hgap.2⟩
      have hnotBetweenFin : ¬ (left < index ∧ index < right) := by
        intro hgap
        apply hbetween
        exact ⟨by simpa using hgap.1, by simpa using hgap.2⟩
      simp [hcurrentIndex, hnotBetweenFin, hnotGapFin]

/-- The distinguished bit of a number consisting of an odd multiple of a
binary power plus a strictly smaller remainder is one. -/
private theorem testBit_true_of_pow_mul_odd_add_lt
    (bit quotient remainder : Nat) (hremainder : remainder < 2 ^ bit) :
    (2 ^ bit * (2 * quotient + 1) + remainder).testBit bit = true := by
  have hpow : 0 < 2 ^ bit := Nat.two_pow_pos _
  have hdiv :
      (2 ^ bit * (2 * quotient + 1) + remainder) / 2 ^ bit =
        2 * quotient + 1 := by
    calc
      (2 ^ bit * (2 * quotient + 1) + remainder) / 2 ^ bit =
          (remainder + 2 ^ bit * (2 * quotient + 1)) / 2 ^ bit := by
            rw [Nat.add_comm]
      _ = remainder / 2 ^ bit + (2 * quotient + 1) :=
          Nat.add_mul_div_left _ _ hpow
      _ = 2 * quotient + 1 := by
          rw [Nat.div_eq_of_lt hremainder, zero_add]
  have hodd : Nat.bodd (2 * quotient + 1) = true := by
    rw [show 2 * quotient + 1 = Nat.succ (2 * quotient) by omega,
      Nat.bodd_succ, Nat.bodd_mul, Nat.bodd_two]
    simp
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
  rw [← Nat.bodd_eq_one_and_ne_zero]
  exact hodd

/-- Every address in an earlier residual block has a later source bit set.
This is the exact arithmetic fact that makes the literal later controlled
gates inactive on already accepted blocks. -/
private theorem residualSupport_testBit_true_of_lt (b : BinaryExpansion N)
    {left right : Fin (b.s + 1)} (hleft : left.val < right.val)
    {index : Nat} (hsupport : b.residualSupport left index) :
    index.testBit (b.ell right) = true := by
  rcases hsupport with ⟨hlower, hupper⟩
  let offset := index - b.tailMass left
  have hindex : index = b.tailMass left + offset := by
    dsimp [offset]
    exact (Nat.add_sub_of_le hlower).symm
  have hoffset : offset < 2 ^ b.ell left := by
    dsimp [offset]
    omega
  have htail := b.tailMass_eq_tailMass_add_current_add_between hleft
  have hgap := b.gapLowerMass_lt_pow hleft
  have hsplit := b.gapLowerMass_eq_betweenMass_add_current hleft
  have hremaind : b.betweenMass left right + offset < 2 ^ b.ell right := by
    calc
      b.betweenMass left right + offset <
          b.betweenMass left right + 2 ^ b.ell left :=
        Nat.add_lt_add_left hoffset _
      _ = b.gapLowerMass left right := hsplit.symm
      _ < 2 ^ b.ell right := hgap
  have hform : index =
      2 ^ b.ell right * (2 * b.residualHigh right + 1) +
        (b.betweenMass left right + offset) := by
    rw [hindex, htail, b.tailMass_eq_residualHigh_mul]
    rw [pow_succ]
    ring
  rw [hform]
  exact testBit_true_of_pow_mul_odd_add_lt
    (b.ell right) (b.residualHigh right)
    (b.betweenMass left right + offset) hremaind

/-- The mass below a source position, its own summand, and the mass above it
form the certified binary expansion.  This is the arithmetic partition used
by the residual-block invariant. -/
theorem prefixMass_add_current_add_tailMass (b : BinaryExpansion N)
    (m : Fin b.s) :
    b.prefixMass m + 2 ^ b.ell m.castSucc + b.tailMass m.castSucc = N := by
  calc
    b.prefixMass m + 2 ^ b.ell m.castSucc + b.tailMass m.castSucc =
        (∑ index : Fin (b.s + 1),
          if index.val < m.val then 2 ^ b.ell index else 0) +
          (∑ index : Fin (b.s + 1),
            if index = m.castSucc then 2 ^ b.ell index else 0) +
          ∑ index : Fin (b.s + 1),
            if m.castSucc.val < index.val then 2 ^ b.ell index else 0 := by
          simp [prefixMass, tailMass]
    _ = ∑ index : Fin (b.s + 1),
        ((if index.val < m.val then 2 ^ b.ell index else 0) +
          (if index = m.castSucc then 2 ^ b.ell index else 0) +
          (if m.castSucc.val < index.val then 2 ^ b.ell index else 0)) := by
          simp_rw [Finset.sum_add_distrib]
    _ = ∑ index : Fin (b.s + 1), 2 ^ b.ell index := by
          apply Finset.sum_congr rfl
          intro index _
          rcases lt_trichotomy index.val m.val with hbelow | hcurrent | habove
          · have hne : index ≠ m.castSucc := by
              intro heq
              subst index
              simp at hbelow
            have htail : ¬ m.castSucc.val < index.val := by
              simp only [Fin.val_castSucc]
              omega
            simp only [hbelow, if_true, hne, if_false, htail, add_zero]
          · have heq : index = m.castSucc := Fin.ext (by simpa using hcurrent)
            subst index
            simp only [Fin.val_castSucc, lt_self_iff_false, if_false,
              if_true, zero_add, add_zero]
          · have hne : index ≠ m.castSucc := by
              intro heq
              subst index
              simp at habove
            have hbelow : ¬ index.val < m.val := by omega
            have htail : m.castSucc.val < index.val := by
              simp only [Fin.val_castSucc]
              omega
            simp only [hbelow, if_false, hne, htail, if_true,
              zero_add]
    _ = N := b.sum_powers.symm

/-- The same three-way binary partition in the generic source-position
notation used by the induction. -/
theorem lowerMass_add_current_add_tailMass (b : BinaryExpansion N)
    (m : Fin b.s) :
    b.lowerMass m.castSucc + 2 ^ b.ell m.castSucc + b.tailMass m.castSucc = N := by
  simpa using b.prefixMass_add_current_add_tailMass m

/-- After stage `m`, the remaining binary mass is exactly the tail above
source bit `m`. -/
theorem N_sub_lowerMass_succ_eq_tailMass (b : BinaryExpansion N)
    (m : Fin b.s) :
    N - b.lowerMass m.succ = b.tailMass m.castSucc := by
  have hpartition := b.lowerMass_add_current_add_tailMass m
  rw [← b.lowerMass_succ m] at hpartition
  omega

/-- A later source block (including its own interval) lies entirely below an
earlier source block.  This is the finite-support ordering from which the
residual-block orthogonality follows. -/
theorem tailMass_add_current_le_tailMass_of_lt (b : BinaryExpansion N)
    {left right : Fin (b.s + 1)} (hleft : left.val < right.val) :
    b.tailMass right + 2 ^ b.ell right ≤ b.tailMass left := by
  calc
    b.tailMass right + 2 ^ b.ell right =
        (∑ index : Fin (b.s + 1),
          if right.val < index.val then 2 ^ b.ell index else 0) +
          ∑ index : Fin (b.s + 1),
            if index = right then 2 ^ b.ell index else 0 := by
          simp [tailMass]
    _ = ∑ index : Fin (b.s + 1),
        ((if right.val < index.val then 2 ^ b.ell index else 0) +
          if index = right then 2 ^ b.ell index else 0) := by
          rw [Finset.sum_add_distrib]
    _ ≤ ∑ index : Fin (b.s + 1),
        if left.val < index.val then 2 ^ b.ell index else 0 := by
          apply Finset.sum_le_sum
          intro index _
          by_cases htail : right.val < index.val
          · have hleftIndex : left.val < index.val := lt_trans hleft htail
            have hne : index ≠ right := by
              intro heq
              subst index
              exact (Nat.lt_irrefl right.val) htail
            simp [htail, hleftIndex, hne]
          · by_cases hcurrent : index = right
            · subst index
              simp [hleft]
            · simp [htail, hcurrent]
    _ = b.tailMass left := by rfl

/-- Distinct source blocks have disjoint interval supports. -/
theorem residualSupport_disjoint_of_lt (b : BinaryExpansion N)
    {left right : Fin (b.s + 1)} (hleft : left.val < right.val)
    (index : Nat) :
    ¬ (b.residualSupport left index ∧ b.residualSupport right index) := by
  intro hsupport
  rcases hsupport with ⟨hleftSupport, hrightSupport⟩
  have horder := b.tailMass_add_current_le_tailMass_of_lt hleft
  unfold residualSupport at hleftSupport hrightSupport
  omega

/-- The raw aligned blocks used by the induction are orthogonal because
their supports are disjoint.  This is stated at the raw-vector layer so it
can be used before the stage coefficients are normalized. -/
theorem inner_residualBlock_eq_zero_of_lt (b : BinaryExpansion N)
    {left right : Fin (b.s + 1)} (hleft : left.val < right.val) :
    inner ℂ (b.residualBlock left) (b.residualBlock right) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro index _
  by_cases hleftSupport : b.residualSupport left index.val
  · have hrightSupport : ¬ b.residualSupport right index.val := by
      intro hright
      exact b.residualSupport_disjoint_of_lt hleft index ⟨hleftSupport, hright⟩
    rw [b.residualBlock_apply_of_not_support right index hrightSupport]
    simp
  · rw [b.residualBlock_apply_of_not_support left index hleftSupport]
    simp

@[simp]
theorem prefixMass_zero (b : BinaryExpansion N) :
    b.prefixMass ⟨0, b.s_pos⟩ = 0 := by
  unfold prefixMass
  simp

/-- The lower prefix together with its next source bit is bounded by the
certified binary sum.  This is the arithmetic fact that makes every source
rotation denominator positive. -/
theorem prefixMass_add_current_le (b : BinaryExpansion N) (m : Fin b.s) :
    b.prefixMass m + 2 ^ b.ell m.castSucc ≤ N := by
  calc
    b.prefixMass m + 2 ^ b.ell m.castSucc =
        (∑ index : Fin (b.s + 1),
          if index.val < m.val then 2 ^ b.ell index else 0) +
          ∑ index : Fin (b.s + 1),
            if index = m.castSucc then 2 ^ b.ell index else 0 := by
          simp [prefixMass]
    _ = ∑ index : Fin (b.s + 1),
        ((if index.val < m.val then 2 ^ b.ell index else 0) +
          if index = m.castSucc then 2 ^ b.ell index else 0) := by
          rw [Finset.sum_add_distrib]
    _ ≤ ∑ index : Fin (b.s + 1), 2 ^ b.ell index := by
          apply Finset.sum_le_sum
          intro index _
          by_cases hbelow : index.val < m.val
          · have hne : index ≠ m.castSucc := by
              intro heq
              subst index
              simp at hbelow
            simp [hbelow, hne]
          · by_cases hcurrent : index = m.castSucc
            · subst index
              simp
            · simp [hbelow, hcurrent]
    _ = N := b.sum_powers.symm

/-- Every Algorithm-1 rotation denominator is strictly positive. -/
theorem prefixMass_lt (b : BinaryExpansion N) (m : Fin b.s) :
    b.prefixMass m < N := by
  have hbound := b.prefixMass_add_current_le m
  have hpositive : 0 < 2 ^ b.ell m.castSucc := Nat.two_pow_pos _
  omega

/-- The squared retained amplitude used by one source rotation. -/
def sourceRatio (b : BinaryExpansion N) (m : Fin b.s) : ℝ :=
  ((2 ^ b.ell m.castSucc : Nat) : ℝ) /
    ((N - b.prefixMass m : Nat) : ℝ)

theorem sourceRatio_nonneg (b : BinaryExpansion N) (m : Fin b.s) :
    0 ≤ b.sourceRatio m := by
  unfold sourceRatio
  positivity

theorem sourceRatio_le_one (b : BinaryExpansion N) (m : Fin b.s) :
    b.sourceRatio m ≤ 1 := by
  have hsum := b.prefixMass_add_current_le m
  have hdenNat : 0 < N - b.prefixMass m := Nat.sub_pos_of_lt (b.prefixMass_lt m)
  have hnumNat : 2 ^ b.ell m.castSucc ≤ N - b.prefixMass m := by
    omega
  have hden : (0 : ℝ) < ((N - b.prefixMass m : Nat) : ℝ) := by
    exact_mod_cast hdenNat
  have hnum : ((2 ^ b.ell m.castSucc : Nat) : ℝ) ≤
      ((N - b.prefixMass m : Nat) : ℝ) := by
    exact_mod_cast hnumNat
  unfold sourceRatio
  apply (div_le_iff₀ hden).mpr
  simpa using hnum

/-- The real coefficient of the not-yet-opened aligned block at a source
position.  Its square is precisely the remaining binary mass divided by
`N`. -/
def residualWeight (b : BinaryExpansion N) (m : Fin (b.s + 1)) : ℝ :=
  Real.sqrt
    (((N - b.lowerMass m : Nat) : ℝ) / (N : ℝ))

/-- The real coefficient of one accepted aligned block.  Tensoring this
coefficient with its normalized Walsh block gives amplitude `1 / sqrt N` on
that block's support. -/
def blockWeight (b : BinaryExpansion N) (m : Fin (b.s + 1)) : ℝ :=
  Real.sqrt
    (((2 ^ b.ell m : Nat) : ℝ) / (N : ℝ))

@[simp]
theorem residualWeight_nonneg (b : BinaryExpansion N) (m : Fin (b.s + 1)) :
    0 ≤ b.residualWeight m :=
  Real.sqrt_nonneg _

@[simp]
theorem blockWeight_nonneg (b : BinaryExpansion N) (m : Fin (b.s + 1)) :
    0 ≤ b.blockWeight m :=
  Real.sqrt_nonneg _

/-- The initial residual has unit coefficient. -/
theorem residualWeight_zero (b : BinaryExpansion N) : b.residualWeight 0 = 1 := by
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt b.N_pos
  unfold residualWeight
  rw [b.lowerMass_zero, Nat.sub_zero, div_self hN, Real.sqrt_one]

/-- `sourceRatio` is the current summand divided by the residual mass in the
generic source-position notation. -/
theorem sourceRatio_eq_current_over_residual (b : BinaryExpansion N)
    (m : Fin b.s) :
    b.sourceRatio m =
      ((2 ^ b.ell m.castSucc : Nat) : ℝ) /
        ((N - b.lowerMass m.castSucc : Nat) : ℝ) := by
  simp [sourceRatio]

/-! The next two scalar lemmas isolate the only square-root algebra used by
the residual invariant.  They are real equalities; the circuit action later
uses their canonical coercions to complex amplitudes. -/

private theorem sqrt_mass_mul_sqrt_ratio (mass part total : Nat)
    (hmass : 0 < mass) (htotal : 0 < total) :
    Real.sqrt ((mass : ℝ) / (total : ℝ)) *
        Real.sqrt ((part : ℝ) / (mass : ℝ)) =
      Real.sqrt ((part : ℝ) / (total : ℝ)) := by
  have hmassReal : (mass : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hmass
  have htotalReal : (total : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt htotal
  rw [← Real.sqrt_mul (by positivity : 0 ≤ (mass : ℝ) / (total : ℝ))]
  congr 1
  field_simp [hmassReal, htotalReal]

private theorem sqrt_mass_mul_sqrt_complement (mass part total : Nat)
    (hmass : 0 < mass) (hpart : part ≤ mass) (htotal : 0 < total) :
    Real.sqrt ((mass : ℝ) / (total : ℝ)) *
        Real.sqrt (1 - (part : ℝ) / (mass : ℝ)) =
      Real.sqrt (((mass - part : Nat) : ℝ) / (total : ℝ)) := by
  have hmassReal : (mass : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hmass
  have htotalReal : (total : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt htotal
  rw [← Real.sqrt_mul (by positivity : 0 ≤ (mass : ℝ) / (total : ℝ))]
  congr 1
  rw [Nat.cast_sub hpart]
  field_simp [hmassReal, htotalReal]

/-- The Algorithm-1 rotation angle at one binary gap.  At `m = 0` its
denominator is `N`, since the prefix mass is empty. -/
def sourceAngle (b : BinaryExpansion N) (m : Fin b.s) : ℝ :=
  -2 * Real.arccos
    (Real.sqrt (b.sourceRatio m))

/-- The `|1⟩` coefficient retained by the source rotation is the square root
of its declared binary-mass ratio. -/
theorem cos_half_sourceAngle (b : BinaryExpansion N) (m : Fin b.s) :
    Real.cos (b.sourceAngle m / 2) = Real.sqrt (b.sourceRatio m) := by
  have hnonneg := b.sourceRatio_nonneg m
  have hsqrt_nonneg : 0 ≤ Real.sqrt (b.sourceRatio m) := Real.sqrt_nonneg _
  have hsqrt_le_one : Real.sqrt (b.sourceRatio m) ≤ 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · simpa using b.sourceRatio_le_one m
  unfold sourceAngle
  rw [show (-2 * Real.arccos (Real.sqrt (b.sourceRatio m))) / 2 =
      -Real.arccos (Real.sqrt (b.sourceRatio m)) by ring,
    Real.cos_neg,
    Real.cos_arccos (by linarith) hsqrt_le_one]

/-- The newly opened residual coefficient is the complementary square root.
The negation is exactly the sign appearing in `R_Y(θ)|1⟩`. -/
theorem neg_sin_half_sourceAngle (b : BinaryExpansion N) (m : Fin b.s) :
    -(Real.sin (b.sourceAngle m / 2)) =
      Real.sqrt (1 - b.sourceRatio m) := by
  have hnonneg := b.sourceRatio_nonneg m
  unfold sourceAngle
  rw [show (-2 * Real.arccos (Real.sqrt (b.sourceRatio m))) / 2 =
      -Real.arccos (Real.sqrt (b.sourceRatio m)) by ring,
    Real.sin_neg, neg_neg, Real.sin_arccos,
    Real.sq_sqrt hnonneg]

/-- The retained branch of a source rotation has exactly the accepted-block
coefficient required by the binary partition. -/
theorem residualWeight_mul_cos_half_sourceAngle (b : BinaryExpansion N)
    (m : Fin b.s) :
    b.residualWeight m.castSucc * Real.cos (b.sourceAngle m / 2) =
      b.blockWeight m.castSucc := by
  rw [b.cos_half_sourceAngle, b.sourceRatio_eq_current_over_residual]
  have hmass : 0 < N - b.lowerMass m.castSucc := by
    rw [b.lowerMass_castSucc]
    exact Nat.sub_pos_of_lt (b.prefixMass_lt m)
  simpa [residualWeight, blockWeight] using
    (sqrt_mass_mul_sqrt_ratio
      (N - b.lowerMass m.castSucc) (2 ^ b.ell m.castSucc) N hmass b.N_pos)

/-- The opened branch of a source rotation has the residual coefficient at
the next source position. -/
theorem residualWeight_mul_neg_sin_half_sourceAngle (b : BinaryExpansion N)
    (m : Fin b.s) :
    b.residualWeight m.castSucc * (-(Real.sin (b.sourceAngle m / 2))) =
      b.residualWeight m.succ := by
  rw [b.neg_sin_half_sourceAngle, b.sourceRatio_eq_current_over_residual]
  have hmass : 0 < N - b.lowerMass m.castSucc := by
    rw [b.lowerMass_castSucc]
    exact Nat.sub_pos_of_lt (b.prefixMass_lt m)
  have hpart : 2 ^ b.ell m.castSucc ≤ N - b.lowerMass m.castSucc := by
    rw [b.lowerMass_castSucc]
    have hsum := b.prefixMass_add_current_le m
    omega
  have htail :
      (N - b.lowerMass m.castSucc) - 2 ^ b.ell m.castSucc =
        N - b.lowerMass m.succ := by
    rw [Nat.sub_sub, ← b.lowerMass_succ m]
  have hscalar := sqrt_mass_mul_sqrt_complement
      (N - b.lowerMass m.castSucc) (2 ^ b.ell m.castSucc) N
      hmass hpart b.N_pos
  rw [htail] at hscalar
  simpa [residualWeight] using hscalar

/-- The number of source bit positions opened by one strict binary gap. -/
def gapWidth (b : BinaryExpansion N) (gap : Fin b.s) : Nat :=
  b.ell gap.succ - b.ell gap.castSucc

/-- In the high prefix of the current residual block, the next source bit is
literally `1` and every strictly intermediate gap bit is `0`.  This is the
address factor needed to place the active right-control rotation on its two
physical wires. -/
private theorem residualHighLabel_gap_factor (b : BinaryExpansion N)
    (gap : Fin b.s) :
    b.residualHighLabel gap.castSucc =
      castWidthIndex (by
        have hgap : b.ell gap.castSucc < b.ell gap.succ :=
          b.ell_strict gap.castSucc_lt_succ
        have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
        unfold gapWidth
        omega :
          (b.width - b.ell gap.succ - 1) + b.gapWidth gap =
            b.width - b.ell gap.castSucc - 1)
        (prodEquiv (m := b.width - b.ell gap.succ - 1)
          (n := b.gapWidth gap)
          (b.residualHighLabel gap.succ,
            castWidthIndex (by
              have hgap : b.ell gap.castSucc < b.ell gap.succ :=
                b.ell_strict gap.castSucc_lt_succ
              unfold gapWidth
              omega : 1 + (b.gapWidth gap - 1) = b.gapWidth gap)
              (prodEquiv (m := 1) (n := b.gapWidth gap - 1)
                (1, 0)))) := by
  have hsource : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  have hgapPos : 0 < b.gapWidth gap := by
    unfold gapWidth
    omega
  have hell : b.ell gap.succ = b.ell gap.castSucc + b.gapWidth gap := by
    unfold gapWidth
    omega
  have htail := b.tailMass_eq_pow_add_tailMass_succ gap
  have hnext := b.tailMass_eq_residualHigh_mul gap.succ
  have hfactor : b.tailMass gap.castSucc =
      2 ^ (b.ell gap.castSucc + 1) *
        (2 ^ b.gapWidth gap * b.residualHigh gap.succ +
          2 ^ (b.gapWidth gap - 1)) := by
    have hpowCurrent :
        2 ^ b.ell gap.succ =
          2 ^ (b.ell gap.castSucc + 1) *
            2 ^ (b.gapWidth gap - 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hpowNext :
        2 ^ (b.ell gap.succ + 1) =
          2 ^ (b.ell gap.castSucc + 1) * 2 ^ b.gapWidth gap := by
      rw [← pow_add]
      congr 1
      omega
    rw [htail, hnext, hpowCurrent, hpowNext]
    ring
  have hquot : b.residualHigh gap.castSucc =
      2 ^ b.gapWidth gap * b.residualHigh gap.succ +
        2 ^ (b.gapWidth gap - 1) := by
    change b.tailMass gap.castSucc / 2 ^ (b.ell gap.castSucc + 1) = _
    rw [hfactor, Nat.mul_div_right _ (Nat.two_pow_pos _)]
  apply Fin.ext
  simp only [residualHighLabel_val, castWidthIndex_val, prodEquiv_val]
  simpa [Nat.add_comm] using hquot

/-- Extend the finite source exponent sequence by its final value.  This
auxiliary monotone function exposes the natural-number telescoping lemma for
the literal gap widths. -/
def clampedEll (b : BinaryExpansion N) (index : Nat) : Nat :=
  b.ell ⟨min index b.s, by
    have hle : min index b.s ≤ b.s := Nat.min_le_right _ _
    omega⟩

private theorem clampedEll_monotone (b : BinaryExpansion N) :
    Monotone b.clampedEll := by
  intro left right hleft
  apply b.ell_strict.monotone
  change min left b.s ≤ min right b.s
  exact min_le_min hleft le_rfl

@[simp]
private theorem clampedEll_zero (b : BinaryExpansion N) :
    b.clampedEll 0 = b.first := by
  simp [clampedEll, first]

@[simp]
private theorem clampedEll_last (b : BinaryExpansion N) :
    b.clampedEll b.s = b.last := by
  unfold clampedEll last
  congr 1
  apply Fin.ext
  simp

/-- Strict source gaps telescope exactly to the interval between the lowest
and highest set-bit exponents. -/
theorem sum_gapWidth (b : BinaryExpansion N) :
    ∑ gap : Fin b.s, b.gapWidth gap = b.last - b.first := by
  rw [Finset.sum_fin_eq_sum_range]
  calc
    _ = ∑ index ∈ Finset.range b.s,
        (b.clampedEll (index + 1) - b.clampedEll index) := by
      apply Finset.sum_congr rfl
      intro index hindex
      have hlt : index < b.s := Finset.mem_range.mp hindex
      simp only [dif_pos hlt]
      change b.gapWidth (Fin.mk index hlt) = _
      simp [gapWidth, clampedEll, Nat.min_eq_left (Nat.le_of_lt hlt),
        Nat.min_eq_left (Nat.succ_le_iff.mpr hlt)]
    _ = b.clampedEll b.s - b.clampedEll 0 :=
      Finset.sum_range_tsub (b.clampedEll_monotone) b.s
    _ = b.last - b.first := by simp

/-- Because every source gap is strict, the number of gaps is no larger than
their total width. -/
theorem s_le_gapWidth_sum (b : BinaryExpansion N) :
    b.s ≤ ∑ gap : Fin b.s, b.gapWidth gap := by
  calc
    b.s = ∑ _gap : Fin b.s, 1 := by simp
    _ ≤ ∑ gap : Fin b.s, b.gapWidth gap := by
      apply Finset.sum_le_sum
      intro gap _
      unfold gapWidth
      have hstrict : b.ell gap.castSucc < b.ell gap.succ :=
        b.ell_strict gap.castSucc_lt_succ
      omega

/-- The physical target wire for one member of a binary gap. -/
def gapTargetWire (b : BinaryExpansion N) (gap : Fin b.s)
    (offset : Fin (b.gapWidth gap)) : Fin b.width :=
  WireAddress.littleEndianWire
    ⟨b.ell gap.castSucc + offset.val, by
      have hgap : b.ell gap.castSucc + offset.val < b.ell gap.succ := by
        have hsource : b.ell gap.castSucc < b.ell gap.succ :=
          b.ell_strict gap.castSucc_lt_succ
        have hoffset := offset.isLt
        unfold gapWidth at hoffset
        omega
      have htop : b.ell gap.succ ≤ b.ell (Fin.last b.s) :=
        b.ell_strict.monotone (Fin.le_last gap.succ)
      unfold width last
      omega⟩

private theorem wire_val (b : BinaryExpansion N) (j : Fin (b.s + 1)) :
    (b.wire j).val = b.width - 1 - b.ell j := by
  unfold wire WireAddress.littleEndianWire WireAddress.bitIndex
  dsimp

private theorem highWidth_eq_wire_val (b : BinaryExpansion N)
    (j : Fin (b.s + 1)) :
    b.width - b.ell j - 1 = (b.wire j).val := by
  rw [b.wire_val j]
  have hwidth : b.ell j < b.width := b.ell_lt_width j
  omega

private theorem ell_eq_wire_suffixWidth (b : BinaryExpansion N)
    (j : Fin (b.s + 1)) :
    b.ell j = b.width - (b.wire j).val - 1 := by
  rw [b.wire_val j]
  have hwidth : b.ell j < b.width := b.ell_lt_width j
  omega

private theorem gapTargetWire_val (b : BinaryExpansion N) (gap : Fin b.s)
    (offset : Fin (b.ell gap.succ - b.ell gap.castSucc)) :
    (b.gapTargetWire gap offset).val =
      b.width - 1 - (b.ell gap.castSucc + offset.val) := by
  unfold gapTargetWire WireAddress.littleEndianWire WireAddress.bitIndex
  dsimp

private theorem gapWidth_pred_eq_wire_sub (b : BinaryExpansion N)
    (gap : Fin b.s) :
    b.gapWidth gap - 1 =
      (b.wire gap.castSucc).val - (b.wire gap.succ).val - 1 := by
  rw [b.wire_val gap.castSucc, b.wire_val gap.succ]
  have hsource : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  unfold gapWidth
  omega

private theorem gapRemaining_eq_target_sub (b : BinaryExpansion N)
    (gap : Fin b.s) (offset : Fin (b.gapWidth gap)) :
    b.gapWidth gap - offset.val - 1 =
      (b.gapTargetWire gap offset).val - (b.wire gap.succ).val - 1 := by
  rw [b.wire_val gap.succ, b.gapTargetWire_val gap offset]
  have hsource : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  have hoffset := offset.isLt
  unfold gapWidth at hoffset ⊢
  omega

private theorem gapProcessed_eq_target_suffixWidth (b : BinaryExpansion N)
    (gap : Fin b.s) (offset : Fin (b.gapWidth gap)) :
    offset.val + b.ell gap.castSucc =
      b.width - (b.gapTargetWire gap offset).val - 1 := by
  rw [b.gapTargetWire_val gap offset]
  have hsource : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  have hoffset := offset.isLt
  unfold gapWidth at hoffset
  omega

/-- The high endpoint controls every lower source-gap target from the physical
left after converting the source's little-endian bit positions. -/
theorem wire_succ_lt_gapTargetWire (b : BinaryExpansion N) (gap : Fin b.s)
    (offset : Fin (b.gapWidth gap)) :
    (b.wire gap.succ).val < (b.gapTargetWire gap offset).val := by
  have hgap : b.ell gap.castSucc + offset.val < b.ell gap.succ := by
    have hsource : b.ell gap.castSucc < b.ell gap.succ :=
      b.ell_strict gap.castSucc_lt_succ
    have hoffset := offset.isLt
    unfold gapWidth at hoffset
    omega
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  unfold gapTargetWire wire WireAddress.littleEndianWire WireAddress.bitIndex
  dsimp
  omega

/-- The raw active branch after `processed` right-to-left gap Hadamards.
The five displayed physical factors are, in order: the fixed high source
prefix, the open control at `ell_(m+1)`, the still-zero gap targets, the
already-expanded `|+⟩` target suffix, and the old low Walsh block.  This is
the residual-block invariant in a form that can be consumed directly by the
actual separated-wire lowering. -/
private def gapHPartial (b : BinaryExpansion N) (gap : Fin b.s)
    (processed : Nat) (hprocessed : processed ≤ b.gapWidth gap) :
    HilbertVector (Qubits b.width) :=
  castWidthVec (by
    have hgap : b.ell gap.castSucc < b.ell gap.succ :=
      b.ell_strict gap.castSucc_lt_succ
    have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
    unfold gapWidth at hprocessed ⊢
    omega :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - processed) +
            (processed + b.ell gap.castSucc))) = b.width)
    (HilbertVector.tensor
      (basisKetVec (b.residualHighLabel gap.succ))
      (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (HilbertVector.tensor
          (rawKetZero (b.gapWidth gap - processed))
          (HilbertVector.tensor (gapPlusBlock processed)
            (WalshHadamard.uniformState (b.ell gap.castSucc) :
              HilbertVector (Qubits (b.ell gap.castSucc)))))))

/-- The currently open aligned residual block, split at the next source bit.
The five displayed factors are in physical order: high prefix, next source
bit, strict gap interior, current source bit, and the old low Walsh block.
This is a raw tensor identity derived from `residualBlock_tensor_factor` and
the concrete `residualHighLabel_gap_factor`; it contains no state certificate
or semantic assumption. -/
private theorem residualBlock_gap_rotation_tensor (b : BinaryExpansion N)
    (gap : Fin b.s) :
    b.residualBlock gap.castSucc =
      castWidthVec (by
        have hgap : b.ell gap.castSucc < b.ell gap.succ :=
          b.ell_strict gap.castSucc_lt_succ
        have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
        unfold gapWidth
        omega :
          ((b.width - b.ell gap.succ - 1) +
              (1 + (b.gapWidth gap - 1))) +
              (1 + b.ell gap.castSucc) = b.width)
        (HilbertVector.tensor
          (HilbertVector.tensor
            (basisKetVec (b.residualHighLabel gap.succ))
            (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              (rawKetZero (b.gapWidth gap - 1))))
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
            (WalshHadamard.uniformState (b.ell gap.castSucc) :
              HilbertVector (Qubits (b.ell gap.castSucc))))) := by
  have hgap : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  have hinner : 1 + (b.gapWidth gap - 1) = b.gapWidth gap := by
    unfold gapWidth
    omega
  have hhigh :
      (b.width - b.ell gap.succ - 1) + b.gapWidth gap =
        b.width - b.ell gap.castSucc - 1 := by
    unfold gapWidth
    omega
  have houter :
      (b.width - b.ell gap.castSucc - 1) +
          (1 + b.ell gap.castSucc) = b.width := by
    omega
  have hcombined :
      ((b.width - b.ell gap.succ - 1) + b.gapWidth gap) +
          (1 + b.ell gap.castSucc) = b.width := by
    rw [hhigh]
    exact houter
  have hhighInner :
      (b.width - b.ell gap.succ - 1) +
          (1 + (b.gapWidth gap - 1)) =
        (b.width - b.ell gap.succ - 1) + b.gapWidth gap := by
    rw [hinner]
  have hlabel :
      (basisKetVec (b.residualHighLabel gap.castSucc)) =
        castWidthVec hhigh
          (HilbertVector.tensor
            (basisKetVec (b.residualHighLabel gap.succ))
            (castWidthVec hinner
              (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
                (rawKetZero (b.gapWidth gap - 1))))) := by
    rw [b.residualHighLabel_gap_factor]
    rw [← castWidthVec_ket]
    congr 1
    rw [← raw_tensor_ket]
    congr 1
    rw [← castWidthVec_ket]
    rw [← raw_tensor_ket]
    simp [rawKetZero, basisKetVec, ket1]
  rw [b.residualBlock_tensor_factor gap.castSucc, hlabel]
  rw [castWidthVec_tensor_left_transport hhigh houter]
  have hinnerTensor :
      HilbertVector.tensor
          (basisKetVec (b.residualHighLabel gap.succ))
          (castWidthVec hinner
            (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              (rawKetZero (b.gapWidth gap - 1)))) =
        castWidthVec hhighInner
          (HilbertVector.tensor
            (basisKetVec (b.residualHighLabel gap.succ))
            (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
              (rawKetZero (b.gapWidth gap - 1)))) := by
    simpa using
      (castWidthVec_tensor_right_transport hinner rfl
        (basisKetVec (b.residualHighLabel gap.succ))
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
          (rawKetZero (b.gapWidth gap - 1))))
  rw [hinnerTensor]
  rw [castWidthVec_tensor_left_transport hhighInner hcombined]

/-- The current residual in the literal two-wire orientation of the source
rotation: target `ell_(m+1)` is physical left and its open control
`ell_m` is physical right. -/
private theorem residualBlock_eq_rotationSeparated (b : BinaryExpansion N)
    (gap : Fin b.s) :
    b.residualBlock gap.castSucc =
      atSeparatedVec (b.wire gap.succ) (b.wire gap.castSucc)
        (b.wire_succ_lt_wire gap)
        (castWidthVec (by
          exact b.highWidth_eq_wire_val gap.succ)
          (basisKetVec (b.residualHighLabel gap.succ)))
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
          (ket0 : HilbertVector (Qubits 1)))
        (castWidthVec (by
          exact b.gapWidth_pred_eq_wire_sub gap)
          (rawKetZero (b.gapWidth gap - 1)))
        (castWidthVec (by
          exact b.ell_eq_wire_suffixWidth gap.castSucc)
          (WalshHadamard.uniformState (b.ell gap.castSucc) :
            HilbertVector (Qubits (b.ell gap.castSucc)))) := by
  have hgap : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  let high := (basisKetVec (b.residualHighLabel gap.succ))
  let middle := rawKetZero (b.gapWidth gap - 1)
  let suffix := (WalshHadamard.uniformState (b.ell gap.castSucc) :
    HilbertVector (Qubits (b.ell gap.castSucc)))
  have hcanonical :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) = b.width := by
    unfold gapWidth
    omega
  have hleft :
      ((b.width - b.ell gap.succ - 1) +
          (1 + (b.gapWidth gap - 1))) +
          (1 + b.ell gap.castSucc) =
        (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) := by
    omega
  have hright :
      ((b.width - b.ell gap.succ - 1) +
          ((1 + (b.gapWidth gap - 1)) + 1)) +
          b.ell gap.castSucc =
        (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) := by
    omega
  calc
    b.residualBlock gap.castSucc =
        castWidthVec (by
          have hgap' : b.ell gap.castSucc < b.ell gap.succ :=
            b.ell_strict gap.castSucc_lt_succ
          unfold gapWidth
          omega :
            ((b.width - b.ell gap.succ - 1) +
                (1 + (b.gapWidth gap - 1))) +
                (1 + b.ell gap.castSucc) = b.width)
          (HilbertVector.tensor
            (HilbertVector.tensor high
              (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) middle))
            (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix)) := by
          simpa [high, middle, suffix] using b.residualBlock_gap_rotation_tensor gap
    _ = castWidthVec hcanonical
          (castWidthVec hleft
            (HilbertVector.tensor
              (HilbertVector.tensor high
                (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) middle))
              (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix))) := by
          symm
          simpa using castWidthVec_trans hleft hcanonical _
    _ = castWidthVec hcanonical
          (castWidthVec hright
            (HilbertVector.tensor
              (HilbertVector.tensor high
                (HilbertVector.tensor
                  (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) middle)
                  (ket0 : HilbertVector (Qubits 1))))
              suffix)) := by
          congr 1
          simpa using raw_tensor_rebracket5 high (ket1 : HilbertVector (Qubits 1))
            middle (ket0 : HilbertVector (Qubits 1)) suffix
    _ = atSeparatedVec (b.wire gap.succ) (b.wire gap.castSucc)
          (b.wire_succ_lt_wire gap)
          (castWidthVec (by
            rw [b.wire_val gap.succ]
            omega : b.width - b.ell gap.succ - 1 =
              (b.wire gap.succ).val) high)
          (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
            (ket0 : HilbertVector (Qubits 1)))
          (castWidthVec (by
            rw [b.wire_val gap.castSucc, b.wire_val gap.succ]
            unfold gapWidth
            omega : b.gapWidth gap - 1 =
              (b.wire gap.castSucc).val - (b.wire gap.succ).val - 1) middle)
          (castWidthVec (by
            rw [b.wire_val gap.castSucc]
            omega : b.ell gap.castSucc =
              b.width - (b.wire gap.castSucc).val - 1) suffix) := by
          rw [castWidthVec_trans]
          symm
          simpa using
            (atSeparatedVec_tensor_body_transport
              (b.wire gap.succ) (b.wire gap.castSucc)
              (b.wire_succ_lt_wire gap)
              (by
                exact b.highWidth_eq_wire_val gap.succ)
              (by
                exact b.gapWidth_pred_eq_wire_sub gap)
              (by
                exact b.ell_eq_wire_suffixWidth gap.castSucc)
              high (ket1 : HilbertVector (Qubits 1)) middle
              (ket0 : HilbertVector (Qubits 1)) suffix)

/-- For a not-yet-finished gap, `gapHPartial` has the canonical five-factor
form at the next literal H target.  The equality exposes only concrete
tensor association and the split of a zero register; it is the bridge from
the residual invariant to `openControlledHAt_applyVec_atSeparated`. -/
private theorem gapHPartial_canonical (b : BinaryExpansion N) (gap : Fin b.s)
    (processed : Nat) (hprocessed : processed < b.gapWidth gap) :
    b.gapHPartial gap processed (Nat.le_of_lt hprocessed) =
      castWidthVec (by
        have hgap : b.ell gap.castSucc < b.ell gap.succ :=
          b.ell_strict gap.castSucc_lt_succ
        have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
        unfold gapWidth at hprocessed ⊢
        omega :
          (b.width - b.ell gap.succ - 1) +
            (1 + ((b.gapWidth gap - processed - 1) +
              (1 + (processed + b.ell gap.castSucc)))) = b.width)
        (HilbertVector.tensor
          (basisKetVec (b.residualHighLabel gap.succ))
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
            (HilbertVector.tensor
              (rawKetZero (b.gapWidth gap - processed - 1))
              (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
                (HilbertVector.tensor (gapPlusBlock processed)
                  (WalshHadamard.uniformState (b.ell gap.castSucc) :
                    HilbertVector (Qubits (b.ell gap.castSucc)))))))) := by
  have hgap : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  let suffix := HilbertVector.tensor (gapPlusBlock processed)
    (WalshHadamard.uniformState (b.ell gap.castSucc) :
      HilbertVector (Qubits (b.ell gap.castSucc)))
  have hsplit :
      (b.gapWidth gap - processed - 1) + 1 =
        b.gapWidth gap - processed := by
    omega
  have hzero :
      (b.gapWidth gap - processed) + (processed + b.ell gap.castSucc) =
        (b.gapWidth gap - processed - 1) +
          (1 + (processed + b.ell gap.castSucc)) := by
    omega
  have hsource :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - processed) +
            (processed + b.ell gap.castSucc))) = b.width := by
    unfold gapWidth at hprocessed ⊢
    omega
  have htarget :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - processed - 1) +
            (1 + (processed + b.ell gap.castSucc)))) = b.width := by
    unfold gapWidth at hprocessed ⊢
    omega
  have hzeroState :
      castWidthVec hzero
        (HilbertVector.tensor
          (rawKetZero (b.gapWidth gap - processed)) suffix) =
        HilbertVector.tensor
          (rawKetZero (b.gapWidth gap - processed - 1))
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix) := by
    rw [← raw_tensor_ket0_cast hsplit]
    rw [castWidthVec_tensor_left_transport hsplit hzero]
    simpa [rawKetZero, basisKetVec, ket0] using
      (raw_tensor_assoc
        (rawKetZero (b.gapWidth gap - processed - 1))
        (ket0 : HilbertVector (Qubits 1)) suffix)
  unfold gapHPartial
  change castWidthVec hsource
      (HilbertVector.tensor
        (basisKetVec (b.residualHighLabel gap.succ))
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (HilbertVector.tensor
            (rawKetZero (b.gapWidth gap - processed)) suffix))) = _
  rw [castWidthVec_tensor_two_right_transport hzero hsource htarget]
  rw [hzeroState]

/-- The initial active-zero branch of one source gap, written in the
target-left/control-right orientation of the literal source rotation. -/
private theorem gapHPartial_zero_eq_rotationSeparated
    (b : BinaryExpansion N) (gap : Fin b.s) :
    b.gapHPartial gap 0 (Nat.zero_le _) =
      atSeparatedVec (b.wire gap.succ) (b.wire gap.castSucc)
        (b.wire_succ_lt_wire gap)
        (castWidthVec (by
          exact b.highWidth_eq_wire_val gap.succ)
          (basisKetVec (b.residualHighLabel gap.succ)))
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (ket0 : HilbertVector (Qubits 1)))
        (castWidthVec (by
          exact b.gapWidth_pred_eq_wire_sub gap)
          (rawKetZero (b.gapWidth gap - 1)))
        (castWidthVec (by
          exact b.ell_eq_wire_suffixWidth gap.castSucc)
          (WalshHadamard.uniformState (b.ell gap.castSucc) :
            HilbertVector (Qubits (b.ell gap.castSucc)))) := by
  have hsource : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  have hpositive : 0 < b.gapWidth gap := by
    unfold gapWidth
    omega
  let high := (basisKetVec (b.residualHighLabel gap.succ))
  let middle := rawKetZero (b.gapWidth gap - 1)
  let suffix := (WalshHadamard.uniformState (b.ell gap.castSucc) :
    HilbertVector (Qubits (b.ell gap.castSucc)))
  let innerSource := HilbertVector.tensor
    (ket0 : HilbertVector (Qubits 1))
    (HilbertVector.tensor (gapPlusBlock 0) suffix)
  have hinnerWidth :
      1 + (0 + b.ell gap.castSucc) = 1 + b.ell gap.castSucc := by
    omega
  have hzeroTail :
      castWidthVec (Nat.zero_add (b.ell gap.castSucc))
          (HilbertVector.tensor (gapPlusBlock 0) suffix) = suffix := by
    change castWidthVec (Nat.zero_add (b.ell gap.castSucc))
        (HilbertVector.tensor (rawKetZero 0) suffix) = suffix
    exact raw_ket0_tensor_left_zero suffix
  have hinnerState :
      castWidthVec hinnerWidth innerSource =
        HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix := by
    unfold innerSource
    calc
      castWidthVec hinnerWidth
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
            (HilbertVector.tensor (gapPlusBlock 0) suffix)) =
          castWidthVec rfl
            (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              (castWidthVec (Nat.zero_add (b.ell gap.castSucc))
                (HilbertVector.tensor (gapPlusBlock 0) suffix))) := by
            symm
            simpa using
              (castWidthVec_tensor_right_transport
                (Nat.zero_add (b.ell gap.castSucc)) rfl
                (ket0 : HilbertVector (Qubits 1))
                (HilbertVector.tensor (gapPlusBlock 0) suffix))
      _ = _ := by rw [hzeroTail, castWidthVec_self]
  have hsourceCanonical :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + (0 + b.ell gap.castSucc)))) = b.width := by
    unfold gapWidth
    omega
  have hcanonical :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) = b.width := by
    unfold gapWidth
    omega
  have hright :
      ((b.width - b.ell gap.succ - 1) +
          ((1 + (b.gapWidth gap - 1)) + 1)) +
          b.ell gap.castSucc =
        (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) := by
    omega
  calc
    b.gapHPartial gap 0 (Nat.zero_le _) =
        castWidthVec hsourceCanonical
          (HilbertVector.tensor high
            (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              (HilbertVector.tensor middle innerSource))) := by
          simpa [high, middle, suffix, innerSource] using
            b.gapHPartial_canonical gap 0 hpositive
    _ =
        castWidthVec hcanonical
          (HilbertVector.tensor high
            (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              (HilbertVector.tensor middle
                (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix)))) := by
          rw [castWidthVec_tensor_three_right_transport
            hinnerWidth hsourceCanonical hcanonical]
          rw [hinnerState]
    _ = castWidthVec hcanonical
          (castWidthVec hright
            (HilbertVector.tensor
              (HilbertVector.tensor high
                (HilbertVector.tensor
                  (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) middle)
                  (ket0 : HilbertVector (Qubits 1))))
              suffix)) := by
          congr 1
          simpa using raw_tensor_right_to_separated5 high
            (ket0 : HilbertVector (Qubits 1)) middle
            (ket0 : HilbertVector (Qubits 1)) suffix
    _ = atSeparatedVec (b.wire gap.succ) (b.wire gap.castSucc)
          (b.wire_succ_lt_wire gap)
          (castWidthVec (by
            exact b.highWidth_eq_wire_val gap.succ) high)
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
            (ket0 : HilbertVector (Qubits 1)))
          (castWidthVec (by
            exact b.gapWidth_pred_eq_wire_sub gap) middle)
          (castWidthVec (by
            exact b.ell_eq_wire_suffixWidth gap.castSucc) suffix) := by
          rw [castWidthVec_trans]
          symm
          simpa using
            (atSeparatedVec_tensor_body_transport
              (b.wire gap.succ) (b.wire gap.castSucc)
              (b.wire_succ_lt_wire gap)
              (by
                exact b.highWidth_eq_wire_val gap.succ)
              (by
                exact b.gapWidth_pred_eq_wire_sub gap)
              (by
                exact b.ell_eq_wire_suffixWidth gap.castSucc)
              high (ket0 : HilbertVector (Qubits 1)) middle
              (ket0 : HilbertVector (Qubits 1)) suffix)

/-- The not-yet-finished gap state in the exact separated-wire orientation
of its next literal leading-control H lowering. -/
private theorem gapHPartial_eq_hSeparated (b : BinaryExpansion N)
    (gap : Fin b.s) (processed : Nat)
    (hprocessed : processed < b.gapWidth gap) :
    b.gapHPartial gap processed (Nat.le_of_lt hprocessed) =
      atSeparatedVec (b.wire gap.succ)
        (b.gapTargetWire gap ⟨processed, hprocessed⟩)
        (b.wire_succ_lt_gapTargetWire gap ⟨processed, hprocessed⟩)
        (castWidthVec (by
          exact b.highWidth_eq_wire_val gap.succ)
          (basisKetVec (b.residualHighLabel gap.succ)))
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (ket0 : HilbertVector (Qubits 1)))
        (castWidthVec (by
          exact b.gapRemaining_eq_target_sub gap ⟨processed, hprocessed⟩)
          (rawKetZero (b.gapWidth gap - processed - 1)))
        (castWidthVec (by
          exact b.gapProcessed_eq_target_suffixWidth gap
            ⟨processed, hprocessed⟩)
          (HilbertVector.tensor (gapPlusBlock processed)
            (WalshHadamard.uniformState (b.ell gap.castSucc) :
              HilbertVector (Qubits (b.ell gap.castSucc))))) := by
  have hsource : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  let high := (basisKetVec (b.residualHighLabel gap.succ))
  let middle := rawKetZero (b.gapWidth gap - processed - 1)
  let suffix := HilbertVector.tensor (gapPlusBlock processed)
    (WalshHadamard.uniformState (b.ell gap.castSucc) :
      HilbertVector (Qubits (b.ell gap.castSucc)))
  have hcanonical :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - processed - 1) +
            (1 + (processed + b.ell gap.castSucc)))) = b.width := by
    unfold gapWidth at hprocessed ⊢
    omega
  have hright :
      ((b.width - b.ell gap.succ - 1) +
          ((1 + (b.gapWidth gap - processed - 1)) + 1)) +
          (processed + b.ell gap.castSucc) =
        (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - processed - 1) +
            (1 + (processed + b.ell gap.castSucc)))) := by
    omega
  calc
    b.gapHPartial gap processed (Nat.le_of_lt hprocessed) =
        castWidthVec hcanonical
          (HilbertVector.tensor high
            (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              (HilbertVector.tensor middle
                (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix)))) := by
          simpa [high, middle, suffix] using
            b.gapHPartial_canonical gap processed hprocessed
    _ = castWidthVec hcanonical
          (castWidthVec hright
              (HilbertVector.tensor
              (HilbertVector.tensor high
                (HilbertVector.tensor
                  (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) middle)
                  (ket0 : HilbertVector (Qubits 1))))
              suffix)) := by
          congr 1
          simpa using raw_tensor_right_to_separated5 high
            (ket0 : HilbertVector (Qubits 1)) middle
            (ket0 : HilbertVector (Qubits 1)) suffix
    _ = atSeparatedVec (b.wire gap.succ)
          (b.gapTargetWire gap ⟨processed, hprocessed⟩)
          (b.wire_succ_lt_gapTargetWire gap ⟨processed, hprocessed⟩)
          (castWidthVec (by
            exact b.highWidth_eq_wire_val gap.succ) high)
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
            (ket0 : HilbertVector (Qubits 1)))
          (castWidthVec (by
            exact b.gapRemaining_eq_target_sub gap
              ⟨processed, hprocessed⟩) middle)
          (castWidthVec (by
            exact b.gapProcessed_eq_target_suffixWidth gap
              ⟨processed, hprocessed⟩)
            suffix) := by
          rw [castWidthVec_trans]
          symm
          simpa using
            (atSeparatedVec_tensor_body_transport
              (b.wire gap.succ)
              (b.gapTargetWire gap ⟨processed, hprocessed⟩)
              (b.wire_succ_lt_gapTargetWire gap ⟨processed, hprocessed⟩)
              (by
                exact b.highWidth_eq_wire_val gap.succ)
              (by
                exact b.gapRemaining_eq_target_sub gap
                  ⟨processed, hprocessed⟩)
              (by
                exact b.gapProcessed_eq_target_suffixWidth gap
                  ⟨processed, hprocessed⟩)
              high (ket0 : HilbertVector (Qubits 1)) middle
              (ket0 : HilbertVector (Qubits 1)) suffix)

/-- After the H at offset `processed`, the newly expanded target is the
physical `|+⟩` factor between the remaining zero gap prefix and the already
expanded suffix. -/
private theorem gapHPartial_succ_eq_hSeparatedPlus
    (b : BinaryExpansion N) (gap : Fin b.s) (processed : Nat)
    (hprocessed : processed < b.gapWidth gap) :
    b.gapHPartial gap (processed + 1) (Nat.succ_le_of_lt hprocessed) =
      atSeparatedVec (b.wire gap.succ)
        (b.gapTargetWire gap ⟨processed, hprocessed⟩)
        (b.wire_succ_lt_gapTargetWire gap ⟨processed, hprocessed⟩)
        (castWidthVec (by
          exact b.highWidth_eq_wire_val gap.succ)
          (basisKetVec (b.residualHighLabel gap.succ)))
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (ketPlus : HilbertVector (Qubits 1)))
        (castWidthVec (by
          have hremaining := b.gapRemaining_eq_target_sub gap
            ⟨processed, hprocessed⟩
          omega : b.gapWidth gap - (processed + 1) =
            (b.gapTargetWire gap ⟨processed, hprocessed⟩).val -
              (b.wire gap.succ).val - 1)
          (rawKetZero (b.gapWidth gap - (processed + 1))))
        (castWidthVec (by
          exact b.gapProcessed_eq_target_suffixWidth gap
            ⟨processed, hprocessed⟩)
          (HilbertVector.tensor (gapPlusBlock processed)
            (WalshHadamard.uniformState (b.ell gap.castSucc) :
              HilbertVector (Qubits (b.ell gap.castSucc))))) := by
  have hsourceEll : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  let high := (basisKetVec (b.residualHighLabel gap.succ))
  let middle := rawKetZero (b.gapWidth gap - (processed + 1))
  let suffix := HilbertVector.tensor (gapPlusBlock processed)
    (WalshHadamard.uniformState (b.ell gap.castSucc) :
      HilbertVector (Qubits (b.ell gap.castSucc)))
  let expanded := HilbertVector.tensor (gapPlusBlock (processed + 1))
    (WalshHadamard.uniformState (b.ell gap.castSucc) :
      HilbertVector (Qubits (b.ell gap.castSucc)))
  have htail :
      (processed + 1) + b.ell gap.castSucc =
        1 + (processed + b.ell gap.castSucc) := by
    omega
  have hsource :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - (processed + 1)) +
            ((processed + 1) + b.ell gap.castSucc))) = b.width := by
    unfold gapWidth at hprocessed ⊢
    omega
  have hcanonical :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - (processed + 1)) +
            (1 + (processed + b.ell gap.castSucc)))) = b.width := by
    unfold gapWidth at hprocessed ⊢
    omega
  have hright :
      ((b.width - b.ell gap.succ - 1) +
          ((1 + (b.gapWidth gap - (processed + 1))) + 1)) +
          (processed + b.ell gap.castSucc) =
        (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - (processed + 1)) +
            (1 + (processed + b.ell gap.castSucc)))) := by
    omega
  have hexpanded :
      castWidthVec htail expanded =
        HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1)) suffix := by
    simpa [expanded, suffix] using
      gapPlusBlock_succ_tensor_suffix processed (b.ell gap.castSucc)
        (WalshHadamard.uniformState (b.ell gap.castSucc) :
          HilbertVector (Qubits (b.ell gap.castSucc)))
  unfold gapHPartial
  change castWidthVec hsource
      (HilbertVector.tensor high
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (HilbertVector.tensor middle expanded))) = _
  rw [castWidthVec_tensor_three_right_transport htail hsource hcanonical]
  rw [hexpanded]
  calc
    castWidthVec hcanonical
        (HilbertVector.tensor high
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
            (HilbertVector.tensor middle
              (HilbertVector.tensor (ketPlus : HilbertVector (Qubits 1)) suffix)))) =
        castWidthVec hcanonical
          (castWidthVec hright
            (HilbertVector.tensor
              (HilbertVector.tensor high
                (HilbertVector.tensor
                  (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) middle)
                  (ketPlus : HilbertVector (Qubits 1))))
              suffix)) := by
            congr 1
            simpa using raw_tensor_right_to_separated5 high
              (ket0 : HilbertVector (Qubits 1)) middle
              (ketPlus : HilbertVector (Qubits 1)) suffix
    _ = atSeparatedVec (b.wire gap.succ)
          (b.gapTargetWire gap ⟨processed, hprocessed⟩)
          (b.wire_succ_lt_gapTargetWire gap ⟨processed, hprocessed⟩)
          (castWidthVec (by
            exact b.highWidth_eq_wire_val gap.succ) high)
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
            (ketPlus : HilbertVector (Qubits 1)))
          (castWidthVec (by
            have hremaining := b.gapRemaining_eq_target_sub gap
              ⟨processed, hprocessed⟩
            omega : b.gapWidth gap - (processed + 1) =
              (b.gapTargetWire gap ⟨processed, hprocessed⟩).val -
                (b.wire gap.succ).val - 1) middle)
          (castWidthVec (by
            exact b.gapProcessed_eq_target_suffixWidth gap
              ⟨processed, hprocessed⟩)
            suffix) := by
          rw [castWidthVec_trans]
          symm
          simpa using
            (atSeparatedVec_tensor_body_transport
              (b.wire gap.succ)
              (b.gapTargetWire gap ⟨processed, hprocessed⟩)
              (b.wire_succ_lt_gapTargetWire gap ⟨processed, hprocessed⟩)
              (by
                exact b.highWidth_eq_wire_val gap.succ)
              (by
                have hremaining := b.gapRemaining_eq_target_sub gap
                  ⟨processed, hprocessed⟩
                omega : b.gapWidth gap - (processed + 1) =
                  (b.gapTargetWire gap ⟨processed, hprocessed⟩).val -
                    (b.wire gap.succ).val - 1)
              (by
                exact b.gapProcessed_eq_target_suffixWidth gap
                  ⟨processed, hprocessed⟩)
              high (ket0 : HilbertVector (Qubits 1)) middle
              (ketPlus : HilbertVector (Qubits 1)) suffix)

/-- Once every target in a source gap has been expanded, the final raw
partial branch is precisely the next aligned residual block. -/
private theorem gapHPartial_final_eq_residualBlock
    (b : BinaryExpansion N) (gap : Fin b.s) :
    b.gapHPartial gap (b.gapWidth gap) (Nat.le_refl _) =
      b.residualBlock gap.succ := by
  have hsource : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  have hell : b.gapWidth gap + b.ell gap.castSucc = b.ell gap.succ := by
    unfold gapWidth at ⊢
    omega
  let high := basisKetVec (b.residualHighLabel gap.succ)
  let suffix := HilbertVector.tensor (gapPlusBlock (b.gapWidth gap))
    (WalshHadamard.uniformState (b.ell gap.castSucc) :
      HilbertVector (Qubits (b.ell gap.castSucc)))
  have hzeroWidth :
      (b.gapWidth gap - b.gapWidth gap) +
          (b.gapWidth gap + b.ell gap.castSucc) =
        b.gapWidth gap + b.ell gap.castSucc := by
    omega
  have hremaining : b.gapWidth gap - b.gapWidth gap = 0 :=
    Nat.sub_self _
  have hzeroState :
      castWidthVec hzeroWidth
          (HilbertVector.tensor
            (rawKetZero (b.gapWidth gap - b.gapWidth gap)) suffix) =
        suffix := by
    simpa only using raw_ket0_tensor_left_of_eq_zero hremaining suffix
  have hsourceWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - b.gapWidth gap) +
            (b.gapWidth gap + b.ell gap.castSucc))) = b.width := by
    unfold gapWidth
    omega
  have htargetWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + (b.gapWidth gap + b.ell gap.castSucc)) = b.width := by
    unfold gapWidth
    omega
  have hresidualWidth :
      (b.width - b.ell gap.succ - 1) +
          (1 + b.ell gap.succ) = b.width := by
    omega
  unfold gapHPartial
  change castWidthVec hsourceWidth
      (HilbertVector.tensor high
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (HilbertVector.tensor
            (rawKetZero (b.gapWidth gap - b.gapWidth gap)) suffix))) = _
  rw [castWidthVec_tensor_two_right_transport
    hzeroWidth hsourceWidth htargetWidth]
  rw [hzeroState]
  unfold suffix high
  rw [gapPlusBlock_eq_walshUniform,
    walshUniform_tensor_walshUniform]
  rw [castWidthVec_tensor_two_right_transport
    hell htargetWidth hresidualWidth]
  rw [castWidthVec_walshUniform]
  simpa using (b.residualBlock_tensor_factor gap.succ).symm

/-- An empty actual circuit on a fixed-width register. -/
def idleCircuit (width : Nat) : UnitaryCircuit (Qubits width) :=
  UnitaryCircuit.identity (Qubits width) [] List.nodup_nil

/-- Canonical physical placement of a complete fixed-width register. -/
private def rangeLayout (width : Nat) : QubitLayout width where
  physical_idx := fun index => index.val
  physical_idx_injective := fun _ _ h => Fin.ext h

@[simp]
private theorem rangeLayout_systemIdx (width : Nat) :
    (rangeLayout width).systemIdx = List.range width := by
  simp [rangeLayout, QubitLayout.systemIdx, List.ofFn_eq_pmap]

@[simp]
theorem idleCircuit_physical_idx_subset_range (width : Nat) :
    (idleCircuit width).physical_idx ⊆ List.range width := by
  simp [idleCircuit, UnitaryCircuit.identity]

/-- The source's initial X gates, in its increasing set-bit order. -/
def initialXLayer (b : BinaryExpansion N) : UnitaryCircuit (Qubits b.width) :=
  UnitaryCircuit.indexedProductNamed "sv24-algorithm1-initial-x" b.s
    (idleCircuit b.width)
    (fun j => xAtWire (b.wire j.succ))

/-- Flipping a bit strictly above an existing natural address is ordinary
addition.  This is the local arithmetic bridge from the addressed-X
permutation to the source's sum of distinct binary powers. -/
private theorem xor_two_pow_eq_add_of_lt {value bit : Nat}
    (hvalue : value < 2 ^ bit) :
    value ^^^ 2 ^ bit = value + 2 ^ bit := by
  have hor : 2 ^ bit + value = 2 ^ bit ||| value := by
    simpa using Nat.two_pow_add_eq_or_of_lt hvalue 1
  rw [Nat.add_comm, hor]
  apply Nat.eq_of_testBit_eq
  intro index
  rw [Nat.testBit_xor, Nat.testBit_or]
  by_cases hindex : index = bit
  · subst index
    simp [Nat.testBit_lt_two_pow hvalue]
  · have hpow : (2 ^ bit).testBit index = false :=
      Nat.testBit_two_pow_of_ne (Ne.symm hindex)
    simp [hpow]

/-- A finite strict family of binary powers stays below the next strict
exponent.  It is the no-carry bound needed by the X-fold invariant. -/
private theorem sum_pow_lt_pow_of_strictMono {count : Nat}
    (exponent : Fin count → Nat) (hstrict : StrictMono exponent)
    (upper : Nat) (hupper : ∀ index, exponent index < upper) :
    (∑ index, 2 ^ exponent index) < 2 ^ upper := by
  rw [← Finset.sum_image hstrict.injective.injOn]
  exact Nat.geomSum_lt (m := 2) (s := Finset.univ.image exponent)
    (n := upper) (by omega) (by
      intro current hcurrent
      rcases Finset.mem_image.mp hcurrent with ⟨index, -, rfl⟩
      exact hupper index)

/-- Folding XORs of strictly increasing binary powers is their ordinary
sum.  The proof consumes the list in source order and applies the preceding
no-carry bound before each final flip. -/
private theorem foldl_xorPow_eq_sum_of_strictMono :
    ∀ (count : Nat) (exponent : Fin count → Nat), StrictMono exponent →
      (List.ofFn exponent).foldl (fun value bit => value ^^^ 2 ^ bit) 0 =
        ∑ index, 2 ^ exponent index := by
  intro count
  induction count with
  | zero =>
      intro exponent _
      simp
  | succ count induction =>
      intro exponent hstrict
      have hprefix : StrictMono (fun index : Fin count => exponent index.castSucc) := by
        intro left right hleft
        apply hstrict
        simpa using hleft
      have hbound :
          (∑ index : Fin count, 2 ^ exponent index.castSucc) <
            2 ^ exponent (Fin.last count) := by
        apply sum_pow_lt_pow_of_strictMono
          (fun index : Fin count => exponent index.castSucc) hprefix
          (exponent (Fin.last count))
        intro index
        apply hstrict
        change index.val < (Fin.last count).val
        simpa only [Fin.val_last] using index.isLt
      rw [List.ofFn_succ_last, List.foldl_append]
      simp only [List.foldl_cons]
      rw [induction _ hprefix, xor_two_pow_eq_add_of_lt hbound,
        Fin.sum_univ_castSucc]
      simp

/-- Taking values commutes with the literal fold of addressed bit flips. -/
private theorem foldl_flipBit_values (width : Nat) :
    ∀ (wires : List (Fin width)) (label : Fin (2 ^ width)),
      (wires.foldl (fun current wire => WireAddress.flipBit wire current) label).val =
        (wires.map fun wire => (WireAddress.bitIndex wire).val).foldl
          (fun current bit => current ^^^ 2 ^ bit) label.val := by
  intro wires label
  induction wires generalizing label with
  | nil => simp
  | cons wire wires induction =>
      rw [List.foldl_cons, List.map_cons, List.foldl_cons,
        induction (WireAddress.flipBit wire label)]
      rfl

/-- The computational-basis address reached by the literal initial X layer.
Keeping this fold explicit lets the later binary-address lemma connect actual
addressed-X execution to the aligned residual block, rather than treating the
source bit pattern as an external state certificate. -/
def initialXLabel (b : BinaryExpansion N) : Fin (2 ^ b.width) :=
  (List.ofFn fun j : Fin b.s => b.wire j.succ).foldl
    (fun label wire => WireAddress.flipBit wire label) 0

/-- The literal initial-X address is exactly the sum of all source powers
strictly above `ell_0`, i.e. the base of the first aligned residual block. -/
theorem initialXLabel_val (b : BinaryExpansion N) :
    b.initialXLabel.val = b.tailMass 0 := by
  unfold initialXLabel
  rw [foldl_flipBit_values]
  have hmap :
      (List.ofFn fun j : Fin b.s => b.wire j.succ).map
          (fun wire => (WireAddress.bitIndex wire).val) =
        List.ofFn (fun j : Fin b.s => b.ell j.succ) := by
    simpa only [Function.comp_apply, b.bitIndex_wire] using
      (List.ofFn_comp' (fun j : Fin b.s => b.wire j.succ)
        (fun wire => (WireAddress.bitIndex wire).val)).symm
  rw [hmap]
  simp only [Fin.val_zero]
  have hstrict : StrictMono (fun j : Fin b.s => b.ell j.succ) := by
    intro left right hleft
    apply b.ell_strict
    simpa using hleft
  rw [foldl_xorPow_eq_sum_of_strictMono b.s
    (fun j : Fin b.s => b.ell j.succ) hstrict]
  unfold tailMass
  rw [Fin.sum_univ_succ]
  simp

theorem initialXLabel_eq_tailMass (b : BinaryExpansion N) :
    b.initialXLabel =
      ⟨b.tailMass 0, by
        have hbound : b.tailMass 0 < 2 ^ b.width := by
          let firstGap : Fin b.s := ⟨0, b.s_pos⟩
          have hpartition :=
            b.prefixMass_add_current_add_tailMass firstGap
          have hpositive : 0 < 2 ^ b.ell firstGap.castSucc :=
            Nat.two_pow_pos _
          rw [b.prefixMass_zero] at hpartition
          have htail : b.tailMass firstGap.castSucc < N := by
            omega
          have hfits : N ≤ 2 ^ b.width := b.fits_proof
          have hzero : firstGap.castSucc = (0 : Fin (b.s + 1)) := by
            apply Fin.ext
            rfl
          rw [hzero] at htail
          exact htail.trans_le hfits
        exact hbound⟩ := by
  apply Fin.ext
  exact b.initialXLabel_val

@[simp]
theorem xAtWire_applyNormalized_ket {width : Nat} (wire : Fin width)
    (label : Fin (2 ^ width)) :
    (xAtWire wire).applyNormalized (NormalizedVector.ket label) =
      NormalizedVector.ket (WireAddress.flipBit wire label) := by
  exact QubitPrimitive.circuit_applyNormalized_ket (.x wire) label

/-- The initial layer's zero-input action follows its literal increasing
addressed-X schedule exactly. -/
theorem initialXLayer_apply_zero (b : BinaryExpansion N) :
    b.initialXLayer.applyNormalized
        (NormalizedVector.ket (R := Qubits b.width) 0) =
      NormalizedVector.ket b.initialXLabel := by
  unfold initialXLayer
  rw [UnitaryCircuit.applyNormalized_indexedProductNamed]
  have hmap :
      List.ofFn (fun j : Fin b.s => xAtWire (b.wire j.succ)) =
        (List.ofFn fun j : Fin b.s => b.wire j.succ).map xAtWire := by
    exact List.ofFn_comp' (fun j : Fin b.s => b.wire j.succ) xAtWire
  rw [hmap]
  have hfold : ∀ (wires : List (Fin b.width)) (label : Fin (2 ^ b.width)),
      (wires.map xAtWire).foldl
          (fun state circuit => circuit.applyNormalized state)
          (NormalizedVector.ket label) =
        NormalizedVector.ket
          (wires.foldl (fun current wire => WireAddress.flipBit wire current) label) := by
    intro wires label
    induction wires generalizing label with
    | nil => simp
    | cons wire wires ih =>
        simp [ih, xAtWire_applyNormalized_ket]
  simpa [initialXLabel, idleCircuit] using
    hfold (List.ofFn fun j : Fin b.s => b.wire j.succ) 0

/-- Raw-vector form of the literal addressed-X prefix action. -/
theorem initialXLayer_applyVec_zero (b : BinaryExpansion N) :
    b.initialXLayer.applyVec
        ((NormalizedVector.ket (R := Qubits b.width) 0) :
          HilbertVector (Qubits b.width)) =
      (NormalizedVector.ket (R := Qubits b.width) b.initialXLabel :
        HilbertVector (Qubits b.width)) := by
  simpa using congrArg
    (fun state : NormalizedVector (Qubits b.width) =>
      (state : HilbertVector (Qubits b.width)))
    b.initialXLayer_apply_zero

theorem initialXLayer_physical_idx_subset_range (b : BinaryExpansion N) :
    b.initialXLayer.physical_idx ⊆ List.range b.width := by
  rw [← rangeLayout_systemIdx b.width]
  unfold initialXLayer
  apply UnitaryCircuit.indexedProductNamed_physical_idx_subset_layout
      (layout := rangeLayout b.width)
  · simp
  · intro j
    simp

/-- The parallel Hadamard layer on the low `ell_0` source bits.  The literal
recursive tensor circuit is lifted to the low suffix by identities. -/
def lowHadamardLayer (b : BinaryExpansion N) : UnitaryCircuit (Qubits b.width) :=
  castWidth (by
    have hle : b.first ≤ b.last :=
      b.ell_strict.monotone (Fin.zero_le _)
    unfold width
    omega : (b.width - b.first) + b.first = b.width)
    (UnitaryCircuit.prodRight (m := b.width - b.first)
      (WalshHadamard.hadamardLayer b.first))

theorem lowHadamardLayer_physical_idx_subset_range (b : BinaryExpansion N) :
    b.lowHadamardLayer.physical_idx ⊆ List.range b.width := by
  have hlow :
      (UnitaryCircuit.prodRight (m := b.width - b.first)
        (WalshHadamard.hadamardLayer b.first)).physical_idx ⊆
        List.range ((b.width - b.first) + b.first) :=
    UnitaryCircuit.prodRight_physical_idx_subset_range _ (by simp)
  simpa [lowHadamardLayer,
    Nat.sub_add_cancel (Nat.le_of_lt b.first_lt_width)] using hlow

/-- The literal low Hadamard layer has the expected tensor action on any
unchanged high register.  This is the initial aligned-block semantic step;
it uses the actual `WalshHadamard.hadamardLayer` circuit, not an abstract
preparation witness. -/
theorem lowHadamardLayer_applyNormalized_tensor (b : BinaryExpansion N)
    (high : NormalizedVector (Qubits (b.width - b.first))) :
    b.lowHadamardLayer.applyNormalized
        (castWidthState (by
          have hle : b.first ≤ b.last :=
            b.ell_strict.monotone (Fin.zero_le _)
          unfold width
          omega : (b.width - b.first) + b.first = b.width)
          (high.tensor (NormalizedVector.ket (R := Qubits b.first) 0))) =
      castWidthState (by
        have hle : b.first ≤ b.last :=
          b.ell_strict.monotone (Fin.zero_le _)
        unfold width
        omega : (b.width - b.first) + b.first = b.width)
        (high.tensor (WalshHadamard.uniformState b.first)) := by
  unfold lowHadamardLayer
  rw [castWidth_applyNormalized, prodRight_applyNormalized_tensor,
    UnitaryCircuit.applyNormalized, WalshHadamard.hadamardLayer_matrix,
    WalshHadamard.hadamardLayerOperator_apply_zero]

/-- Raw-vector version of the initial low Hadamard action.  This is the
linear form used when the exact residual block is subsequently split into
accepted and remaining branches. -/
theorem lowHadamardLayer_applyVec_tensor (b : BinaryExpansion N)
    (high : HilbertVector (Qubits (b.width - b.first))) :
    b.lowHadamardLayer.applyVec
        (castWidthVec (by
          have hle : b.first ≤ b.last :=
            b.ell_strict.monotone (Fin.zero_le _)
          unfold width
          omega : (b.width - b.first) + b.first = b.width)
          (HilbertVector.tensor high
            (NormalizedVector.ket (R := Qubits b.first) 0))) =
      castWidthVec (by
        have hle : b.first ≤ b.last :=
          b.ell_strict.monotone (Fin.zero_le _)
        unfold width
        omega : (b.width - b.first) + b.first = b.width)
        (HilbertVector.tensor high
          (WalshHadamard.uniformState b.first : HilbertVector (Qubits b.first))) := by
  have hzero :
      (WalshHadamard.hadamardLayerOperator b.first).applyVec
          ((NormalizedVector.ket (R := Qubits b.first) 0) :
            HilbertVector (Qubits b.first)) =
        (WalshHadamard.uniformState b.first : HilbertVector (Qubits b.first)) := by
    simpa only [UnitaryOperator.apply_coe] using congrArg
      (fun state : NormalizedVector (Qubits b.first) =>
        (state : HilbertVector (Qubits b.first)))
      (WalshHadamard.hadamardLayerOperator_apply_zero (n := b.first))
  unfold lowHadamardLayer
  rw [castWidth_applyVec, prodRight_applyVec_tensor,
    UnitaryCircuit.applyVec, WalshHadamard.hadamardLayer_matrix, hzero]

/-- The open-controlled Hadamards across one source binary gap.  Each entry
is the same literal decomposed `openControlledHAt` circuit used by the
resource ledger; `indexedProductNamed` fixes Algorithm 1's increasing target
order. -/
def gapHadamardLayer (b : BinaryExpansion N) (gap : Fin b.s) :
    UnitaryCircuit (Qubits b.width) :=
  UnitaryCircuit.indexedProductNamed "sv24-algorithm1-open-controlled-hadamards"
    (b.ell gap.succ - b.ell gap.castSucc)
    (idleCircuit b.width)
    (fun offset =>
      openControlledHAt (b.wire gap.succ) (b.gapTargetWire gap offset)
        (b.wire_succ_lt_gapTargetWire gap offset))

theorem gapHadamardLayer_physical_idx_subset_range (b : BinaryExpansion N)
    (gap : Fin b.s) :
    (b.gapHadamardLayer gap).physical_idx ⊆ List.range b.width := by
  rw [← rangeLayout_systemIdx b.width]
  unfold gapHadamardLayer
  apply UnitaryCircuit.indexedProductNamed_physical_idx_subset_layout
      (layout := rangeLayout b.width)
  · simp
  · intro offset
    simpa using
      (openControlledHAt_physical_idx_subset_range
        (b.wire gap.succ) (b.gapTargetWire gap offset)
        (b.wire_succ_lt_gapTargetWire gap offset))

/-- One source binary-gap stage.  The first stage is Algorithm 1's initial
rotation; all later stages use an open-controlled rotation. -/
def gapStage (b : BinaryExpansion N) (gap : Fin b.s) :
    UnitaryCircuit (Qubits b.width) :=
  if _ : gap.val = 0 then
    UnitaryCircuit.seq (rotYAtWire (b.wire gap.succ) (b.sourceAngle gap))
      (b.gapHadamardLayer gap)
  else
    UnitaryCircuit.seq
      (openControlledRotYAt (b.wire gap.succ) (b.wire gap.castSucc)
        (b.wire_succ_lt_wire gap) (b.sourceAngle gap))
      (b.gapHadamardLayer gap)

theorem gapStage_physical_idx_subset_range (b : BinaryExpansion N)
    (gap : Fin b.s) :
    (b.gapStage gap).physical_idx ⊆ List.range b.width := by
  unfold gapStage
  split_ifs with hfirst
  · apply UnitaryCircuit.seq_physical_idx_subset
    · exact rotYAtWire_physical_idx_subset_range _ _
    · exact b.gapHadamardLayer_physical_idx_subset_range gap
  · apply UnitaryCircuit.seq_physical_idx_subset
    · exact openControlledRotYAt_physical_idx_subset_range _ _ _ _
    · exact b.gapHadamardLayer_physical_idx_subset_range gap

/-- The direct Algorithm-1 gate schedule before its harmless explicit
full-register identity placement is appended. -/
def algorithm1RawCircuit (b : BinaryExpansion N) : UnitaryCircuit (Qubits b.width) :=
  UnitaryCircuit.indexedProductNamed "sv24-algorithm1-gaps" b.s
    (UnitaryCircuit.seq (b.initialXLayer) (b.lowHadamardLayer))
    (fun gap => b.gapStage gap)

theorem algorithm1RawCircuit_physical_idx_subset_range (b : BinaryExpansion N) :
    b.algorithm1RawCircuit.physical_idx ⊆ List.range b.width := by
  rw [← rangeLayout_systemIdx b.width]
  unfold algorithm1RawCircuit
  apply UnitaryCircuit.indexedProductNamed_physical_idx_subset_layout
      (layout := rangeLayout b.width)
  · apply UnitaryCircuit.seq_physical_idx_subset
    · simpa using b.initialXLayer_physical_idx_subset_range
    · simpa using b.lowHadamardLayer_physical_idx_subset_range
  · intro gap
    simpa using b.gapStage_physical_idx_subset_range gap

/-- The complete actual Algorithm-1 preparation circuit at its intrinsic width
`ell_s + 1`.  The final identity records the canonical full footprint needed
when this circuit is paired with another register; it contributes no event or
semantic action. -/
def algorithm1Circuit (b : BinaryExpansion N) : UnitaryCircuit (Qubits b.width) :=
  withCanonicalFootprint b.algorithm1RawCircuit

/-- The intrinsic Algorithm-1 literal circuit occupies exactly its complete
intrinsic register, including the explicit no-event identity placement. -/
theorem algorithm1Circuit_physical_idx (b : BinaryExpansion N) :
    b.algorithm1Circuit.physical_idx = List.range b.width := by
  unfold algorithm1Circuit
  exact withCanonicalFootprint_physical_idx _
    b.algorithm1RawCircuit_physical_idx_subset_range

/-- The same literal preparation widened to any caller-chosen endpoint width
by a high all-zero identity tensor.  This is the circuit needed when the
Fourier endpoint width exceeds `ell_s + 1`; it introduces no new gate event. -/
def algorithm1CircuitPadded (b : BinaryExpansion N) {t : Nat}
    (hwidth : b.width ≤ t) : UnitaryCircuit (Qubits t) :=
  withCanonicalFootprint (padHigh hwidth b.algorithm1Circuit)

theorem algorithm1CircuitPadded_physical_idx (b : BinaryExpansion N) {t : Nat}
    (hwidth : b.width ≤ t) :
    (b.algorithm1CircuitPadded hwidth).physical_idx = List.range t := by
  unfold algorithm1CircuitPadded
  apply withCanonicalFootprint_physical_idx
  unfold padHigh
  have intrinsic : b.algorithm1Circuit.physical_idx ⊆ List.range b.width := by
    rw [b.algorithm1Circuit_physical_idx]
    exact fun _ member => member
  have padded :
      (UnitaryCircuit.prodRight (m := t - b.width) b.algorithm1Circuit).physical_idx ⊆
        List.range ((t - b.width) + b.width) :=
    UnitaryCircuit.prodRight_physical_idx_subset_range _ intrinsic
  simpa [Nat.sub_add_cancel hwidth] using padded

@[simp]
theorem algorithm1CircuitPadded_eventTrace (b : BinaryExpansion N) {t : Nat}
    (hwidth : b.width ≤ t) :
    (b.algorithm1CircuitPadded hwidth).eventTrace = b.algorithm1Circuit.eventTrace := by
  simp [algorithm1CircuitPadded]

@[simp]
theorem algorithm1CircuitPadded_eventCost (b : BinaryExpansion N) {t : Nat}
    (hwidth : b.width ≤ t) :
    (b.algorithm1CircuitPadded hwidth).eventCost = b.algorithm1Circuit.eventCost := by
  simp [algorithm1CircuitPadded]

@[simp]
theorem algorithm1CircuitPadded_evaluatedEventDepth (b : BinaryExpansion N)
    {t : Nat} (hwidth : b.width ≤ t) (assign : Resource.Event .quantum → Nat) :
    (b.algorithm1CircuitPadded hwidth).evaluatedEventDepth assign =
      b.algorithm1Circuit.evaluatedEventDepth assign := by
  simp [algorithm1CircuitPadded]

end BinaryExpansion

@[simp]
theorem rotY_eventTrace (θ : ℝ) :
    (rotY θ).eventTrace = [(rotYLeaf θ).event] :=
  rfl

@[simp]
theorem rotY_matrix (θ : ℝ) : (rotY θ).matrix = rotYOp θ :=
  rfl

/-- Raw computational-basis action of the literal `R_Y` gate on `|0⟩`.
Keeping this at the raw-vector layer lets the Algorithm-1 residual branch be
split linearly without pretending that either summand is normalized. -/
theorem rotY_applyVec_ket0 (θ : ℝ) :
    (rotY θ).applyVec (ket0 : HilbertVector (Qubits 1)) =
      (Real.cos (θ / 2) : ℂ) • (ket0 : HilbertVector (Qubits 1)) +
        (Real.sin (θ / 2) : ℂ) • (ket1 : HilbertVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext index
  fin_cases index <;>
    simp [UnitaryCircuit.applyVec, rotYOp, ket0, ket1, NormalizedVector.ket_apply,
      PiLp.smul_apply, PiLp.add_apply]

/-- Raw computational-basis action of the literal `R_Y` gate on `|1⟩`.
The sign here is the one used by the source angle `-2 arccos(√r)`. -/
theorem rotY_applyVec_ket1 (θ : ℝ) :
    (rotY θ).applyVec (ket1 : HilbertVector (Qubits 1)) =
      (-(Real.sin (θ / 2)) : ℂ) • (ket0 : HilbertVector (Qubits 1)) +
        (Real.cos (θ / 2) : ℂ) • (ket1 : HilbertVector (Qubits 1)) := by
  apply WithLp.ofLp_injective
  funext index
  fin_cases index <;>
    simp [UnitaryCircuit.applyVec, rotYOp, ket0, ket1, NormalizedVector.ket_apply,
      PiLp.smul_apply, PiLp.add_apply]

private theorem rotYOp_applyVec_ket1 (θ : ℝ) :
    (rotYOp θ).applyVec (ket1 : HilbertVector (Qubits 1)) =
      (-(Real.sin (θ / 2)) : ℂ) •
          (ket0 : HilbertVector (Qubits 1)) +
        (Real.cos (θ / 2) : ℂ) •
          (ket1 : HilbertVector (Qubits 1)) := by
  have h := rotY_applyVec_ket1 θ
  change (rotY θ).matrix.applyVec _ = _ at h
  rw [rotY_matrix] at h
  exact h

/-- The literal addressed `R_Y` coordinate acts on a target-one tensor
factor with the signed raw branch decomposition.  This is the direct
operator/matrix consequence used only for Algorithm 1's first, genuinely
uncontrolled source rotation. -/
private theorem rotYAtWire_applyVec_tensor_ket1 {width : Nat}
    (wire : Fin width) (θ : ℝ)
    (left : HilbertVector (Qubits wire.val))
    (right : HilbertVector (Qubits (width - wire.val - 1))) :
    (rotYAtWire wire θ).applyVec
        (castWidthVec (by omega : wire.val + 1 + (width - wire.val - 1) = width)
          (HilbertVector.tensor
            (HilbertVector.tensor left (ket1 : HilbertVector (Qubits 1))) right)) =
      (-(Real.sin (θ / 2)) : ℂ) •
          castWidthVec (by omega : wire.val + 1 + (width - wire.val - 1) = width)
            (HilbertVector.tensor
              (HilbertVector.tensor left (ket0 : HilbertVector (Qubits 1))) right) +
        (Real.cos (θ / 2) : ℂ) •
          castWidthVec (by omega : wire.val + 1 + (width - wire.val - 1) = width)
            (HilbertVector.tensor
              (HilbertVector.tensor left (ket1 : HilbertVector (Qubits 1))) right) := by
  unfold rotYAtWire
  rw [atWire_applyVec_tensor, rotY_applyVec_ket1]
  simp only [HilbertVector.tensor_add, HilbertVector.add_tensor,
    HilbertVector.tensor_smul, HilbertVector.smul_tensor,
    castWidthVec_add, castWidthVec_smul]

/-- Raw-vector form of `H |0⟩ = |+⟩`, exposed for the controlled-H gap
induction. -/
theorem H_applyVec_ket0 :
    H.applyVec (ket0 : HilbertVector (Qubits 1)) =
      (ketPlus : HilbertVector (Qubits 1)) := by
  have normalized := congrArg
    (fun state : NormalizedVector (Qubits 1) =>
      (state : HilbertVector (Qubits 1))) H_apply_ket0
  simpa only [UnitaryCircuit.applyNormalized_coe] using normalized

/-- The metadata-free Hadamard operator has the same raw `|0⟩` action as its
literal elementary circuit. -/
theorem HOp_applyVec_ket0 :
    HOp.applyVec (ket0 : HilbertVector (Qubits 1)) =
      (ketPlus : HilbertVector (Qubits 1)) := by
  have h := H_applyVec_ket0
  change H.matrix.applyVec _ = _ at h
  rw [H_matrix] at h
  exact h

@[simp]
private theorem basisKetVec_zero_one :
    basisKetVec (0 : Fin (2 ^ 1)) =
      (ket0 : HilbertVector (Qubits 1)) :=
  rfl

@[simp]
private theorem basisKetVec_one_one :
    basisKetVec (1 : Fin (2 ^ 1)) =
      (ket1 : HilbertVector (Qubits 1)) :=
  rfl

private theorem fin_two_eq_zero_or_one (index : Fin (2 ^ 1)) :
    index = 0 ∨ index = 1 := by
  fin_cases index
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Equality of finite-dimensional unitaries can be checked on the raw
computational basis without expanding a composite matrix. -/
private theorem unitary_eq_of_applyVec_ket {R : Register}
    (left right : UnitaryOperator R)
    (happly : ∀ input : R.Index,
      left.applyVec
          (NormalizedVector.ket (R := R) input : HilbertVector R) =
        right.applyVec
          (NormalizedVector.ket (R := R) input : HilbertVector R)) :
    left = right := by
  apply Subtype.ext
  ext output input
  have point := congrArg (fun state : HilbertVector R => state output)
    (happly input)
  change HilbertOperator.applyVec (left : HilbertOperator R)
      (NormalizedVector.ket input : HilbertVector R) output =
    HilbertOperator.applyVec (right : HilbertOperator R)
      (NormalizedVector.ket input : HilbertVector R) output at point
  simpa only [HilbertOperator.applyVec_ket] using point

@[simp]
private theorem XOp_applyVec_ket0 :
    XOp.applyVec (ket0 : HilbertVector (Qubits 1)) =
      (ket1 : HilbertVector (Qubits 1)) := by
  have h := congrArg
    (fun state : NormalizedVector (Qubits 1) =>
      (state : HilbertVector (Qubits 1))) X_apply_ket0
  simpa only [UnitaryCircuit.applyNormalized_coe, UnitaryCircuit.applyVec, X_matrix] using h

@[simp]
private theorem XOp_applyVec_ket1 :
    XOp.applyVec (ket1 : HilbertVector (Qubits 1)) =
      (ket0 : HilbertVector (Qubits 1)) := by
  have h := congrArg
    (fun state : NormalizedVector (Qubits 1) =>
      (state : HilbertVector (Qubits 1))) X_apply_ket1
  simpa only [UnitaryCircuit.applyNormalized_coe, UnitaryCircuit.applyVec, X_matrix] using h

@[simp]
private theorem CNOT_applyVec_ket0_tensor_ket0 :
    CNOT.applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (ket0 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (ket0 : HilbertVector (Qubits 1)) := by
  have h := congrArg
    (fun state : NormalizedVector (Qubits 2) =>
      (state : HilbertVector (Qubits 2))) CNOT_apply_ket0_tensor_ket0
  simpa only [UnitaryCircuit.applyNormalized_coe, NormalizedVector.coe_tensor] using h

@[simp]
private theorem CNOT_applyVec_ket0_tensor_ket1 :
    CNOT.applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (ket1 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (ket1 : HilbertVector (Qubits 1)) := by
  have h := congrArg
    (fun state : NormalizedVector (Qubits 2) =>
      (state : HilbertVector (Qubits 2))) CNOT_apply_ket0_tensor_ket1
  simpa only [UnitaryCircuit.applyNormalized_coe, NormalizedVector.coe_tensor] using h

@[simp]
private theorem CNOT_applyVec_ket1_tensor_ket0 :
    CNOT.applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
          (ket0 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
        (ket1 : HilbertVector (Qubits 1)) := by
  have h := congrArg
    (fun state : NormalizedVector (Qubits 2) =>
      (state : HilbertVector (Qubits 2))) CNOT_apply_ket1_tensor_ket0
  simpa only [UnitaryCircuit.applyNormalized_coe, NormalizedVector.coe_tensor] using h

@[simp]
private theorem CNOT_applyVec_ket1_tensor_ket1 :
    CNOT.applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
          (ket1 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
        (ket0 : HilbertVector (Qubits 1)) := by
  have h := congrArg
    (fun state : NormalizedVector (Qubits 2) =>
      (state : HilbertVector (Qubits 2))) CNOT_apply_ket1_tensor_ket1
  simpa only [UnitaryCircuit.applyNormalized_coe, NormalizedVector.coe_tensor] using h

private theorem CNOT_applyVec_ket0_tensor
    (target : HilbertVector (Qubits 1)) :
    CNOT.applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) target) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) target := by
  rw [single_qubit_vec_decomp target]
  simp only [HilbertVector.tensor_add, HilbertVector.tensor_smul,
    UnitaryCircuit.applyVec_add, UnitaryCircuit.applyVec_smul,
    CNOT_applyVec_ket0_tensor_ket0, CNOT_applyVec_ket0_tensor_ket1]

private theorem CNOT_applyVec_ket1_tensor
    (target : HilbertVector (Qubits 1)) :
    CNOT.applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) target) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
        (XOp.applyVec target) := by
  rw [single_qubit_vec_decomp target]
  simp only [HilbertVector.tensor_add, HilbertVector.tensor_smul,
    UnitaryCircuit.applyVec_add, UnitaryCircuit.applyVec_smul,
    UnitaryOperator.applyVec_add, UnitaryOperator.applyVec_smul,
    CNOT_applyVec_ket1_tensor_ket0, CNOT_applyVec_ket1_tensor_ket1,
    XOp_applyVec_ket0, XOp_applyVec_ket1]

private theorem targetRotY_matrix_tensor (θ : ℝ) :
    (targetRotY θ).matrix =
      UnitaryOperator.tensor (1 : UnitaryOperator (Qubits 1))
        (rotYOp θ) := by
  apply Subtype.ext
  simp [targetRotY, rotY_matrix]

private theorem controlX_matrix_tensor :
    controlX.matrix =
      UnitaryOperator.tensor XOp (1 : UnitaryOperator (Qubits 1)) := by
  apply Subtype.ext
  simp [controlX, X_matrix]

private theorem controlXParallelTargetRotY_matrix_tensor (θ : ℝ) :
    (controlXParallelTargetRotY θ).matrix =
      UnitaryOperator.tensor XOp (rotYOp θ) := by
  apply Subtype.ext
  simp [controlXParallelTargetRotY, X_matrix, rotY_matrix]

private theorem targetRotYParallelRightControlX_matrix_tensor (θ : ℝ) :
    (targetRotYParallelRightControlX θ).matrix =
      UnitaryOperator.tensor (rotYOp θ) XOp := by
  apply Subtype.ext
  simp [targetRotYParallelRightControlX, X_matrix, rotY_matrix]

private theorem targetRotY_applyVec_tensor (θ : ℝ)
    (control target : HilbertVector (Qubits 1)) :
    (targetRotY θ).applyVec (HilbertVector.tensor control target) =
      HilbertVector.tensor control ((rotYOp θ).applyVec target) := by
  change (targetRotY θ).matrix.applyVec _ = _
  rw [targetRotY_matrix_tensor, UnitaryOperator.tensor_applyVec_tensor,
    UnitaryOperator.one_applyVec]

private theorem controlX_applyVec_tensor
    (control target : HilbertVector (Qubits 1)) :
    controlX.applyVec (HilbertVector.tensor control target) =
      HilbertVector.tensor (XOp.applyVec control) target := by
  change controlX.matrix.applyVec _ = _
  rw [controlX_matrix_tensor, UnitaryOperator.tensor_applyVec_tensor,
    UnitaryOperator.one_applyVec]

private theorem controlXParallelTargetRotY_applyVec_tensor (θ : ℝ)
    (control target : HilbertVector (Qubits 1)) :
    (controlXParallelTargetRotY θ).applyVec
        (HilbertVector.tensor control target) =
      HilbertVector.tensor (XOp.applyVec control)
        ((rotYOp θ).applyVec target) := by
  change (controlXParallelTargetRotY θ).matrix.applyVec _ = _
  rw [controlXParallelTargetRotY_matrix_tensor,
    UnitaryOperator.tensor_applyVec_tensor]

private theorem targetFirstRotY_applyVec_tensor (θ : ℝ)
    (target control : HilbertVector (Qubits 1)) :
    (targetFirstRotY θ).applyVec
        (HilbertVector.tensor target control) =
      HilbertVector.tensor ((rotYOp θ).applyVec target) control := by
  rw [targetFirstRotY, prodLeft_applyVec_tensor]
  change HilbertVector.tensor ((rotY θ).matrix.applyVec target) control = _
  rw [rotY_matrix]

private theorem rightControlX_applyVec_tensor
    (target control : HilbertVector (Qubits 1)) :
    rightControlX.applyVec (HilbertVector.tensor target control) =
      HilbertVector.tensor target (XOp.applyVec control) := by
  rw [rightControlX, prodRight_applyVec_tensor]
  change HilbertVector.tensor target (X.matrix.applyVec control) = _
  rw [X_matrix]

private theorem targetRotYParallelRightControlX_applyVec_tensor (θ : ℝ)
    (target control : HilbertVector (Qubits 1)) :
    (targetRotYParallelRightControlX θ).applyVec
        (HilbertVector.tensor target control) =
      HilbertVector.tensor ((rotYOp θ).applyVec target)
        (XOp.applyVec control) := by
  change (targetRotYParallelRightControlX θ).matrix.applyVec _ = _
  rw [targetRotYParallelRightControlX_matrix_tensor,
    UnitaryOperator.tensor_applyVec_tensor]

private def rightCNOTPrimitive : QubitPrimitive 2 :=
  .cnot (1 : Fin 2) 0 (by omega)

private theorem rightControlledCNOT_applyVec_basis
    (label : Fin (2 ^ 2)) :
    rightControlledCNOT.applyVec (basisKetVec label) =
      basisKetVec (rightCNOTPrimitive.applyLabel label) := by
  have h := congrArg
    (fun state : NormalizedVector (Qubits 2) =>
      (state : HilbertVector (Qubits 2)))
    (QubitPrimitive.circuit_applyNormalized_ket rightCNOTPrimitive label)
  simpa only [rightControlledCNOT, rightCNOTPrimitive,
    UnitaryCircuit.applyNormalized_coe, basisKetVec] using h

private theorem rightControlledCNOT_applyVec_tensor_basis
    (target control : Fin (2 ^ 1)) :
    rightControlledCNOT.applyVec
        (HilbertVector.tensor (basisKetVec target) (basisKetVec control)) =
      basisKetVec
        (rightCNOTPrimitive.applyLabel
          (prodEquiv (m := 1) (n := 1) (target, control))) := by
  rw [raw_tensor_ket, rightControlledCNOT_applyVec_basis]

private theorem rightControlledCNOT_applyVec_basis00 :
    rightControlledCNOT.applyVec
        (HilbertVector.tensor
          (basisKetVec (0 : Fin (2 ^ 1)))
          (basisKetVec (0 : Fin (2 ^ 1)))) =
      HilbertVector.tensor
        (basisKetVec (0 : Fin (2 ^ 1)))
        (basisKetVec (0 : Fin (2 ^ 1))) := by
  rw [rightControlledCNOT_applyVec_tensor_basis, raw_tensor_ket]
  congr 1

private theorem rightControlledCNOT_applyVec_basis10 :
    rightControlledCNOT.applyVec
        (HilbertVector.tensor
          (basisKetVec (1 : Fin (2 ^ 1)))
          (basisKetVec (0 : Fin (2 ^ 1)))) =
      HilbertVector.tensor
        (basisKetVec (1 : Fin (2 ^ 1)))
        (basisKetVec (0 : Fin (2 ^ 1))) := by
  rw [rightControlledCNOT_applyVec_tensor_basis, raw_tensor_ket]
  congr 1

private theorem rightControlledCNOT_applyVec_basis01 :
    rightControlledCNOT.applyVec
        (HilbertVector.tensor
          (basisKetVec (0 : Fin (2 ^ 1)))
          (basisKetVec (1 : Fin (2 ^ 1)))) =
      HilbertVector.tensor
        (basisKetVec (1 : Fin (2 ^ 1)))
        (basisKetVec (1 : Fin (2 ^ 1))) := by
  rw [rightControlledCNOT_applyVec_tensor_basis, raw_tensor_ket]
  congr 1

private theorem rightControlledCNOT_applyVec_basis11 :
    rightControlledCNOT.applyVec
        (HilbertVector.tensor
          (basisKetVec (1 : Fin (2 ^ 1)))
          (basisKetVec (1 : Fin (2 ^ 1)))) =
      HilbertVector.tensor
        (basisKetVec (0 : Fin (2 ^ 1)))
        (basisKetVec (1 : Fin (2 ^ 1))) := by
  rw [rightControlledCNOT_applyVec_tensor_basis, raw_tensor_ket]
  congr 1

@[simp]
private theorem rightControlledCNOT_applyVec_ket0_tensor_ket0 :
    rightControlledCNOT.applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (ket0 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (ket0 : HilbertVector (Qubits 1)) := by
  simpa only [basisKetVec_zero_one] using
    rightControlledCNOT_applyVec_basis00

@[simp]
private theorem rightControlledCNOT_applyVec_ket1_tensor_ket0 :
    rightControlledCNOT.applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
          (ket0 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
        (ket0 : HilbertVector (Qubits 1)) := by
  simpa only [basisKetVec_zero_one, basisKetVec_one_one] using
    rightControlledCNOT_applyVec_basis10

@[simp]
private theorem rightControlledCNOT_applyVec_ket0_tensor_ket1 :
    rightControlledCNOT.applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (ket1 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
        (ket1 : HilbertVector (Qubits 1)) := by
  simpa only [basisKetVec_zero_one, basisKetVec_one_one] using
    rightControlledCNOT_applyVec_basis01

@[simp]
private theorem rightControlledCNOT_applyVec_ket1_tensor_ket1 :
    rightControlledCNOT.applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
          (ket1 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (ket1 : HilbertVector (Qubits 1)) := by
  simpa only [basisKetVec_zero_one, basisKetVec_one_one] using
    rightControlledCNOT_applyVec_basis11

private theorem rightControlledCNOT_applyVec_tensor_ket0
    (target : HilbertVector (Qubits 1)) :
    rightControlledCNOT.applyVec
        (HilbertVector.tensor target (ket0 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor target (ket0 : HilbertVector (Qubits 1)) := by
  rw [single_qubit_vec_decomp target]
  simp only [HilbertVector.add_tensor, HilbertVector.smul_tensor,
    UnitaryCircuit.applyVec_add, UnitaryCircuit.applyVec_smul,
    rightControlledCNOT_applyVec_ket0_tensor_ket0,
    rightControlledCNOT_applyVec_ket1_tensor_ket0]

private theorem rightControlledCNOT_applyVec_tensor_ket1
    (target : HilbertVector (Qubits 1)) :
    rightControlledCNOT.applyVec
        (HilbertVector.tensor target (ket1 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (XOp.applyVec target)
        (ket1 : HilbertVector (Qubits 1)) := by
  rw [single_qubit_vec_decomp target]
  simp only [HilbertVector.add_tensor, HilbertVector.smul_tensor,
    UnitaryCircuit.applyVec_add, UnitaryCircuit.applyVec_smul,
    UnitaryOperator.applyVec_add, UnitaryOperator.applyVec_smul,
    rightControlledCNOT_applyVec_ket0_tensor_ket1,
    rightControlledCNOT_applyVec_ket1_tensor_ket1,
    XOp_applyVec_ket0, XOp_applyVec_ket1]

/-- Composition of two one-qubit Y rotations.  All matrix arithmetic here is
two-dimensional; the two-qubit circuit proofs below use only this result. -/
private theorem rotYOp_mul (left right : ℝ) :
    (rotYOp left : HilbertOperator (Qubits 1)) *
        (rotYOp right : HilbertOperator (Qubits 1)) =
      (rotYOp (left + right) : HilbertOperator (Qubits 1)) := by
  have hhalf : (left + right) / 2 = left / 2 + right / 2 := by
    ring
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [rotYOp, Matrix.mul_apply, Fin.sum_univ_two, hhalf,
      Real.sin_add, Real.cos_add] <;>
    ring

private theorem rotYOp_zero :
    (rotYOp 0 : HilbertOperator (Qubits 1)) = 1 := by
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [rotYOp]

private theorem rotYOp_neg_mul_rotYOp (θ : ℝ) :
    (rotYOp (-θ) : HilbertOperator (Qubits 1)) *
        (rotYOp θ : HilbertOperator (Qubits 1)) = 1 := by
  rw [rotYOp_mul, neg_add_cancel, rotYOp_zero]

/-- Conjugating a negative Y rotation by Pauli-X reverses its angle. -/
private theorem XOp_mul_rotYOp_neg_mul_XOp (θ : ℝ) :
    ((XOp : HilbertOperator (Qubits 1)) *
        (rotYOp (-θ) : HilbertOperator (Qubits 1))) *
        (XOp : HilbertOperator (Qubits 1)) =
      (rotYOp θ : HilbertOperator (Qubits 1)) := by
  have hhalf : (-θ) / 2 = -(θ / 2) := by
    ring
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [XOp, UnitaryOperator.ofPerm, rotYOp, Matrix.mul_apply,
      Fin.sum_univ_two, Equiv.swap_apply_def, hhalf,
      Real.sin_neg, Real.cos_neg]

private theorem controlledRotY_target_operator (θ : ℝ) :
    (((XOp : HilbertOperator (Qubits 1)) *
          (rotYOp (-(θ / 2)) : HilbertOperator (Qubits 1))) *
        (XOp : HilbertOperator (Qubits 1))) *
        (rotYOp (θ / 2) : HilbertOperator (Qubits 1)) =
      (rotYOp θ : HilbertOperator (Qubits 1)) := by
  rw [XOp_mul_rotYOp_neg_mul_XOp, rotYOp_mul]
  congr 2
  ring

private theorem rotY_cancel_applyVec (θ : ℝ)
    (state : HilbertVector (Qubits 1)) :
    (rotYOp (-θ)).applyVec ((rotYOp θ).applyVec state) = state := by
  change HilbertOperator.applyVec (rotYOp (-θ) : HilbertOperator (Qubits 1))
      (HilbertOperator.applyVec
        (rotYOp θ : HilbertOperator (Qubits 1)) state) = state
  rw [← HilbertOperator.mul_applyVec, rotYOp_neg_mul_rotYOp,
    HilbertOperator.one_applyVec]

private theorem controlledRotY_target_applyVec (θ : ℝ)
    (state : HilbertVector (Qubits 1)) :
    XOp.applyVec
        ((rotYOp (-(θ / 2))).applyVec
          (XOp.applyVec ((rotYOp (θ / 2)).applyVec state))) =
      (rotYOp θ).applyVec state := by
  change HilbertOperator.applyVec (XOp : HilbertOperator (Qubits 1))
      (HilbertOperator.applyVec
        (rotYOp (-(θ / 2)) : HilbertOperator (Qubits 1))
        (HilbertOperator.applyVec (XOp : HilbertOperator (Qubits 1))
          (HilbertOperator.applyVec
            (rotYOp (θ / 2) : HilbertOperator (Qubits 1)) state))) =
    HilbertOperator.applyVec
      (rotYOp θ : HilbertOperator (Qubits 1)) state
  rw [← HilbertOperator.mul_applyVec, ← HilbertOperator.mul_applyVec,
    ← HilbertOperator.mul_applyVec, controlledRotY_target_operator]

private theorem rotYOp_neg_mul_XOp (θ : ℝ) :
    (rotYOp (-θ) : HilbertOperator (Qubits 1)) *
        (XOp : HilbertOperator (Qubits 1)) =
      (XOp : HilbertOperator (Qubits 1)) *
        (rotYOp θ : HilbertOperator (Qubits 1)) := by
  have hhalf : (-θ) / 2 = -(θ / 2) := by
    ring
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [XOp, UnitaryOperator.ofPerm, rotYOp, Matrix.mul_apply,
      Fin.sum_univ_two, Equiv.swap_apply_def, hhalf,
      Real.sin_neg, Real.cos_neg]

private theorem XOp_mul_rotYOp_pi_div_two :
    (XOp : HilbertOperator (Qubits 1)) *
        (rotYOp (Real.pi / 2) : HilbertOperator (Qubits 1)) =
      (HOp : HilbertOperator (Qubits 1)) := by
  have hsqrt_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hsqrt_sq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hinv : invSqrt2 = (Real.sqrt 2 : ℂ) / 2 := by
    rw [NormalizedVector.invSqrt2]
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    calc
      (Real.sqrt 2 : ℂ)⁻¹ * 2 =
          (Real.sqrt 2 : ℂ)⁻¹ *
            ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) := by
              rw [hsqrt_sq]
      _ = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)) *
          (Real.sqrt 2 : ℂ) := by ring
      _ = (Real.sqrt 2 : ℂ) := by
            rw [inv_mul_cancel₀ hsqrt_ne, one_mul]
  have hhalf : (Real.pi / 2) / 2 = Real.pi / 4 := by ring
  ext output input
  fin_cases output <;> fin_cases input <;>
    simp [XOp, UnitaryOperator.ofPerm, HOp, rotYOp, Matrix.mul_apply, hinv, hhalf]

/-- The source's one-CNOT target identity
`R_Y(-pi/4) X R_Y(pi/4) = H`, proved only as a 2×2 matrix equality. -/
private theorem controlledH_target_operator :
    ((rotYOp (-(Real.pi / 4)) : HilbertOperator (Qubits 1)) *
        (XOp : HilbertOperator (Qubits 1))) *
        (rotYOp (Real.pi / 4) : HilbertOperator (Qubits 1)) =
      (HOp : HilbertOperator (Qubits 1)) := by
  rw [rotYOp_neg_mul_XOp, Matrix.mul_assoc, rotYOp_mul]
  rw [show Real.pi / 4 + Real.pi / 4 = Real.pi / 2 by ring,
    XOp_mul_rotYOp_pi_div_two]

private theorem controlledH_target_applyVec
    (state : HilbertVector (Qubits 1)) :
    (rotYOp (-(Real.pi / 4))).applyVec
        (XOp.applyVec ((rotYOp (Real.pi / 4)).applyVec state)) =
      HOp.applyVec state := by
  change HilbertOperator.applyVec
      (rotYOp (-(Real.pi / 4)) : HilbertOperator (Qubits 1))
      (HilbertOperator.applyVec (XOp : HilbertOperator (Qubits 1))
        (HilbertOperator.applyVec
          (rotYOp (Real.pi / 4) : HilbertOperator (Qubits 1)) state)) =
    HilbertOperator.applyVec (HOp : HilbertOperator (Qubits 1)) state
  rw [← HilbertOperator.mul_applyVec, ← HilbertOperator.mul_applyVec,
    controlledH_target_operator]

private theorem controlledRotY_applyVec_ket0_tensor (θ : ℝ)
    (target : HilbertVector (Qubits 1)) :
    (controlledRotY θ).applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) target) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) target := by
  simp only [controlledRotY, UnitaryCircuit.applyVec_seq]
  rw [targetRotY_applyVec_tensor, CNOT_applyVec_ket0_tensor,
    targetRotY_applyVec_tensor, CNOT_applyVec_ket0_tensor,
    rotY_cancel_applyVec]

private theorem controlledRotY_applyVec_ket1_tensor (θ : ℝ)
    (target : HilbertVector (Qubits 1)) :
    (controlledRotY θ).applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) target) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
        ((rotYOp θ).applyVec target) := by
  simp only [controlledRotY, UnitaryCircuit.applyVec_seq]
  rw [targetRotY_applyVec_tensor, CNOT_applyVec_ket1_tensor,
    targetRotY_applyVec_tensor, CNOT_applyVec_ket1_tensor,
    controlledRotY_target_applyVec]

private theorem openControlledRotY_applyVec_ket0_tensor (θ : ℝ)
    (target : HilbertVector (Qubits 1)) :
    (openControlledRotY θ).applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) target) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        ((rotYOp θ).applyVec target) := by
  simp only [openControlledRotY, UnitaryCircuit.applyVec_seq]
  rw [controlXParallelTargetRotY_applyVec_tensor, XOp_applyVec_ket0,
    CNOT_applyVec_ket1_tensor, targetRotY_applyVec_tensor,
    CNOT_applyVec_ket1_tensor, controlX_applyVec_tensor,
    XOp_applyVec_ket1, controlledRotY_target_applyVec]

private theorem openControlledRotY_applyVec_ket1_tensor (θ : ℝ)
    (target : HilbertVector (Qubits 1)) :
    (openControlledRotY θ).applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) target) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) target := by
  simp only [openControlledRotY, UnitaryCircuit.applyVec_seq]
  rw [controlXParallelTargetRotY_applyVec_tensor, XOp_applyVec_ket1,
    CNOT_applyVec_ket0_tensor, targetRotY_applyVec_tensor,
    CNOT_applyVec_ket0_tensor, controlX_applyVec_tensor,
    XOp_applyVec_ket0, rotY_cancel_applyVec]

private theorem controlledH_applyVec_ket0_tensor
    (target : HilbertVector (Qubits 1)) :
    controlledH.applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) target) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) target := by
  simp only [controlledH, UnitaryCircuit.applyVec_seq]
  rw [targetRotY_applyVec_tensor, CNOT_applyVec_ket0_tensor,
    targetRotY_applyVec_tensor, rotY_cancel_applyVec]

private theorem controlledH_applyVec_ket1_tensor
    (target : HilbertVector (Qubits 1)) :
    controlledH.applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) target) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
        (HOp.applyVec target) := by
  simp only [controlledH, UnitaryCircuit.applyVec_seq]
  rw [targetRotY_applyVec_tensor, CNOT_applyVec_ket1_tensor,
    targetRotY_applyVec_tensor, controlledH_target_applyVec]

private theorem openControlledH_applyVec_ket0_tensor_raw
    (target : HilbertVector (Qubits 1)) :
    openControlledH.applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) target) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (HOp.applyVec target) := by
  simp only [openControlledH, UnitaryCircuit.applyVec_seq]
  rw [controlXParallelTargetRotY_applyVec_tensor, XOp_applyVec_ket0,
    CNOT_applyVec_ket1_tensor,
    controlXParallelTargetRotY_applyVec_tensor, XOp_applyVec_ket1,
    controlledH_target_applyVec]

private theorem openControlledH_applyVec_ket1_tensor_raw
    (target : HilbertVector (Qubits 1)) :
    openControlledH.applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) target) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) target := by
  simp only [openControlledH, UnitaryCircuit.applyVec_seq]
  rw [controlXParallelTargetRotY_applyVec_tensor, XOp_applyVec_ket1,
    CNOT_applyVec_ket0_tensor,
    controlXParallelTargetRotY_applyVec_tensor, XOp_applyVec_ket0,
    rotY_cancel_applyVec]

private theorem openControlledRotYRightControl_applyVec_tensor_ket0_raw
    (θ : ℝ) (target : HilbertVector (Qubits 1)) :
    (openControlledRotYRightControl θ).applyVec
        (HilbertVector.tensor target (ket0 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor ((rotYOp θ).applyVec target)
        (ket0 : HilbertVector (Qubits 1)) := by
  simp only [openControlledRotYRightControl, UnitaryCircuit.applyVec_seq]
  rw [targetRotYParallelRightControlX_applyVec_tensor, XOp_applyVec_ket0,
    rightControlledCNOT_applyVec_tensor_ket1,
    targetFirstRotY_applyVec_tensor,
    rightControlledCNOT_applyVec_tensor_ket1,
    rightControlX_applyVec_tensor, XOp_applyVec_ket1,
    controlledRotY_target_applyVec]

private theorem openControlledRotYRightControl_applyVec_tensor_ket1_raw
    (θ : ℝ) (target : HilbertVector (Qubits 1)) :
    (openControlledRotYRightControl θ).applyVec
        (HilbertVector.tensor target (ket1 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor target (ket1 : HilbertVector (Qubits 1)) := by
  simp only [openControlledRotYRightControl, UnitaryCircuit.applyVec_seq]
  rw [targetRotYParallelRightControlX_applyVec_tensor, XOp_applyVec_ket1,
    rightControlledCNOT_applyVec_tensor_ket0,
    targetFirstRotY_applyVec_tensor,
    rightControlledCNOT_applyVec_tensor_ket0,
    rightControlX_applyVec_tensor, XOp_applyVec_ket0,
    rotY_cancel_applyVec]

/-- The literal four-gate lowering has the standard control-on-one rotation
operator, rather than merely the right event labels. -/
theorem controlledRotY_matrix (θ : ℝ) :
    (controlledRotY θ).matrix =
      UnitaryOperator.controlledQubits (rotYOp θ) := by
  apply unitary_eq_of_applyVec_ket
  intro input
  rcases (prodEquiv (m := 1) (n := 1)).surjective input with
    ⟨⟨control, target⟩, rfl⟩
  change (controlledRotY θ).applyVec
      (basisKetVec (prodEquiv (m := 1) (n := 1) (control, target))) =
    (UnitaryOperator.controlledQubits (rotYOp θ)).applyVec
      (basisKetVec (prodEquiv (m := 1) (n := 1) (control, target)))
  rw [← raw_tensor_ket control target]
  rcases fin_two_eq_zero_or_one control with hzero | hone
  · subst control
    rw [basisKetVec_zero_one]
    rw [controlledRotY_applyVec_ket0_tensor,
      UnitaryOperator.controlledQubits_applyVec_ket0_tensor]
  · subst control
    rw [basisKetVec_one_one]
    rw [controlledRotY_applyVec_ket1_tensor,
      UnitaryOperator.controlledQubits_applyVec_ket1_tensor]

/-- The X-conjugated literal lowering has the standard open-control rotation
operator. -/
theorem openControlledRotY_matrix (θ : ℝ) :
    (openControlledRotY θ).matrix =
      UnitaryOperator.controlledQubitsOnZero (rotYOp θ) := by
  apply unitary_eq_of_applyVec_ket
  intro input
  rcases (prodEquiv (m := 1) (n := 1)).surjective input with
    ⟨⟨control, target⟩, rfl⟩
  change (openControlledRotY θ).applyVec
      (basisKetVec (prodEquiv (m := 1) (n := 1) (control, target))) =
    (UnitaryOperator.controlledQubitsOnZero (rotYOp θ)).applyVec
      (basisKetVec (prodEquiv (m := 1) (n := 1) (control, target)))
  rw [← raw_tensor_ket control target]
  rcases fin_two_eq_zero_or_one control with hzero | hone
  · subst control
    rw [basisKetVec_zero_one]
    rw [openControlledRotY_applyVec_ket0_tensor,
      UnitaryOperator.controlledQubitsOnZero_applyVec_ket0_tensor]
  · subst control
    rw [basisKetVec_one_one]
    rw [openControlledRotY_applyVec_ket1_tensor,
      UnitaryOperator.controlledQubitsOnZero_applyVec_ket1_tensor]

/-- The addressed right-control lowering has the corresponding right-control
operator semantics.  The reindex in the right-hand side is mathematical only:
the concrete circuit above is still the two addressed CNOT decomposition. -/
theorem openControlledRotYRightControl_matrix (θ : ℝ) :
    (openControlledRotYRightControl θ).matrix =
      rightControlledQubitsOnZero (rotYOp θ) := by
  apply unitary_eq_of_applyVec_ket
  intro input
  rcases (prodEquiv (m := 1) (n := 1)).surjective input with
    ⟨⟨target, control⟩, rfl⟩
  change (openControlledRotYRightControl θ).applyVec
      (basisKetVec (prodEquiv (m := 1) (n := 1) (target, control))) =
    (rightControlledQubitsOnZero (rotYOp θ)).applyVec
      (basisKetVec (prodEquiv (m := 1) (n := 1) (target, control)))
  rw [← raw_tensor_ket target control]
  rcases fin_two_eq_zero_or_one control with hzero | hone
  · subst control
    rw [basisKetVec_zero_one]
    rw [openControlledRotYRightControl_applyVec_tensor_ket0_raw,
      rightControlledQubitsOnZero_applyVec_tensor_ket0]
  · subst control
    rw [basisKetVec_one_one]
    rw [openControlledRotYRightControl_applyVec_tensor_ket1_raw,
      rightControlledQubitsOnZero_applyVec_tensor_ket1]

/-- The literal one-CNOT lowering has exactly the standard leading-control
Hadamard matrix. -/
theorem controlledH_matrix :
    controlledH.matrix = UnitaryOperator.controlledQubits HOp := by
  apply unitary_eq_of_applyVec_ket
  intro input
  rcases (prodEquiv (m := 1) (n := 1)).surjective input with
    ⟨⟨control, target⟩, rfl⟩
  change controlledH.applyVec
      (basisKetVec (prodEquiv (m := 1) (n := 1) (control, target))) =
    (UnitaryOperator.controlledQubits HOp).applyVec
      (basisKetVec (prodEquiv (m := 1) (n := 1) (control, target)))
  rw [← raw_tensor_ket control target]
  rcases fin_two_eq_zero_or_one control with hzero | hone
  · subst control
    rw [basisKetVec_zero_one]
    rw [controlledH_applyVec_ket0_tensor,
      UnitaryOperator.controlledQubits_applyVec_ket0_tensor]
  · subst control
    rw [basisKetVec_one_one]
    rw [controlledH_applyVec_ket1_tensor,
      UnitaryOperator.controlledQubits_applyVec_ket1_tensor]

/-- The X-conjugated one-CNOT lowering has the standard leading open-control
Hadamard matrix. -/
theorem openControlledH_matrix :
    openControlledH.matrix = UnitaryOperator.controlledQubitsOnZero HOp := by
  apply unitary_eq_of_applyVec_ket
  intro input
  rcases (prodEquiv (m := 1) (n := 1)).surjective input with
    ⟨⟨control, target⟩, rfl⟩
  change openControlledH.applyVec
      (basisKetVec (prodEquiv (m := 1) (n := 1) (control, target))) =
    (UnitaryOperator.controlledQubitsOnZero HOp).applyVec
      (basisKetVec (prodEquiv (m := 1) (n := 1) (control, target)))
  rw [← raw_tensor_ket control target]
  rcases fin_two_eq_zero_or_one control with hzero | hone
  · subst control
    rw [basisKetVec_zero_one]
    rw [openControlledH_applyVec_ket0_tensor_raw,
      UnitaryOperator.controlledQubitsOnZero_applyVec_ket0_tensor]
  · subst control
    rw [basisKetVec_one_one]
    rw [openControlledH_applyVec_ket1_tensor_raw,
      UnitaryOperator.controlledQubitsOnZero_applyVec_ket1_tensor]

/-- State-level form of the literal leading-control open-rotation lowering.
It is obtained by evaluating the matrix equality on an arbitrary normalized
two-qubit state. -/
theorem openControlledRotY_applyNormalized (θ : ℝ)
    (state : NormalizedVector (Qubits 2)) :
    (openControlledRotY θ).applyNormalized state =
      (UnitaryOperator.controlledQubitsOnZero (rotYOp θ)).apply state := by
  change (openControlledRotY θ).matrix.apply state = _
  rw [openControlledRotY_matrix]

theorem controlledRotY_applyNormalized (θ : ℝ)
    (state : NormalizedVector (Qubits 2)) :
    (controlledRotY θ).applyNormalized state =
      (UnitaryOperator.controlledQubits (rotYOp θ)).apply state := by
  change (controlledRotY θ).matrix.apply state = _
  rw [controlledRotY_matrix]

/-- State-level form of the actual right-control lowering used by Algorithm 1
after little-endian source positions are mapped to physical wires. -/
theorem openControlledRotYRightControl_applyNormalized (θ : ℝ)
    (state : NormalizedVector (Qubits 2)) :
    (openControlledRotYRightControl θ).applyNormalized state =
      (rightControlledQubitsOnZero (rotYOp θ)).apply state := by
  change (openControlledRotYRightControl θ).matrix.apply state = _
  rw [openControlledRotYRightControl_matrix]

/-- State-level form of the literal leading-control open-H lowering. -/
theorem openControlledH_applyNormalized (state : NormalizedVector (Qubits 2)) :
    openControlledH.applyNormalized state =
      (UnitaryOperator.controlledQubitsOnZero HOp).apply state := by
  change openControlledH.matrix.apply state = _
  rw [openControlledH_matrix]

theorem controlledH_applyNormalized (state : NormalizedVector (Qubits 2)) :
    controlledH.applyNormalized state =
      (UnitaryOperator.controlledQubits HOp).apply state := by
  change controlledH.matrix.apply state = _
  rw [controlledH_matrix]

/-- Raw-vector form of the literal leading-control open rotation.  The
Algorithm-1 induction uses this linear statement when it separates accepted
and residual blocks before applying the next literal gate. -/
theorem openControlledRotY_applyVec (θ : ℝ)
    (state : HilbertVector (Qubits 2)) :
    (openControlledRotY θ).applyVec state =
      (UnitaryOperator.controlledQubitsOnZero (rotYOp θ)).applyVec state := by
  change (openControlledRotY θ).matrix.applyVec state = _
  rw [openControlledRotY_matrix]

/-- Raw-vector form of the right-control lowering used for the source
little-endian controlled rotations. -/
theorem openControlledRotYRightControl_applyVec (θ : ℝ)
    (state : HilbertVector (Qubits 2)) :
    (openControlledRotYRightControl θ).applyVec state =
      (rightControlledQubitsOnZero (rotYOp θ)).applyVec state := by
  change (openControlledRotYRightControl θ).matrix.applyVec state = _
  rw [openControlledRotYRightControl_matrix]

/-- Raw-vector form of the leading-control open-H lowering. -/
theorem openControlledH_applyVec (state : HilbertVector (Qubits 2)) :
    openControlledH.applyVec state =
      (UnitaryOperator.controlledQubitsOnZero HOp).applyVec state := by
  change openControlledH.matrix.applyVec state = _
  rw [openControlledH_matrix]

/-- The literal source-oriented rotation splits its active `|1⟩⊗|0⟩`
target/control branch with the standard signed `R_Y` amplitudes. -/
theorem openControlledRotYRightControl_applyVec_ket1_tensor_ket0
    (θ : ℝ) :
    (openControlledRotYRightControl θ).applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
          (ket0 : HilbertVector (Qubits 1))) =
      (-(Real.sin (θ / 2)) : ℂ) •
          HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
            (ket0 : HilbertVector (Qubits 1)) +
        (Real.cos (θ / 2) : ℂ) •
          HilbertVector.tensor (ket1 : HilbertVector (Qubits 1))
            (ket0 : HilbertVector (Qubits 1)) := by
  have hrot := rotY_applyVec_ket1 θ
  change (rotY θ).matrix.applyVec _ = _ at hrot
  rw [rotY_matrix] at hrot
  rw [openControlledRotYRightControl_applyVec,
    rightControlledQubitsOnZero_applyVec_tensor_ket0,
    hrot, HilbertVector.add_tensor,
    HilbertVector.smul_tensor, HilbertVector.smul_tensor]

/-- The literal leading-control Hadamard acts on its active `|0⟩⊗|0⟩`
branch exactly as the source gap expansion requires. -/
theorem openControlledH_applyVec_ket0_tensor_ket0 :
    openControlledH.applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
          (ket0 : HilbertVector (Qubits 1))) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
        (ketPlus : HilbertVector (Qubits 1)) := by
  rw [openControlledH_applyVec,
    UnitaryOperator.controlledQubitsOnZero_applyVec_ket0_tensor,
    HOp_applyVec_ket0]

/-- The literal leading-control Hadamard is the identity on its inactive
control-one branch. -/
theorem openControlledH_applyVec_ket1_tensor
    (target : HilbertVector (Qubits 1)) :
    openControlledH.applyVec
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) target) =
      HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) target := by
  rw [openControlledH_applyVec,
    UnitaryOperator.controlledQubitsOnZero_applyVec_ket1_tensor]

/-- On an open control, the literal controlled-H lowering acts as the actual
Hadamard circuit on an arbitrary raw target vector.  The gap-layer induction
uses this linear form after earlier gap targets have become superposed. -/
theorem openControlledH_applyVec_ket0_tensor
    (target : HilbertVector (Qubits 1)) :
    openControlledH.applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) target) =
      HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) (H.applyVec target) := by
  rw [openControlledH_applyVec,
    UnitaryOperator.controlledQubitsOnZero_applyVec_ket0_tensor]
  change HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
      (HOp.applyVec target) = _
  rw [← H_matrix]
  rfl

/-- The source-oriented open rotation retains its right-control operator
meaning after literal placement on separated physical wires. -/
theorem openControlledRotYAt_applyVec_atSeparated {width : Nat}
    (target control : Fin width) (htc : target.val < control.val) (θ : ℝ)
    (leading : HilbertVector (Qubits target.val))
    (body : HilbertVector (Qubits 2))
    (middle : HilbertVector (Qubits (control.val - target.val - 1)))
    (suffix : HilbertVector (Qubits (width - control.val - 1))) :
    (openControlledRotYAt target control htc θ).applyVec
        (atSeparatedVec target control htc leading body middle suffix) =
      atSeparatedVec target control htc leading
        ((rightControlledQubitsOnZero (rotYOp θ)).applyVec body)
        middle suffix := by
  unfold openControlledRotYAt
  rw [atSeparatedWires_applyVec,
    openControlledRotYRightControl_applyVec]

/-- The source gap-H lowering retains its leading open-control operator
meaning after literal placement on separated physical wires. -/
theorem openControlledHAt_applyVec_atSeparated {width : Nat}
    (control target : Fin width) (hct : control.val < target.val)
    (leading : HilbertVector (Qubits control.val))
    (body : HilbertVector (Qubits 2))
    (middle : HilbertVector (Qubits (target.val - control.val - 1)))
    (suffix : HilbertVector (Qubits (width - target.val - 1))) :
    (openControlledHAt control target hct).applyVec
        (atSeparatedVec control target hct leading body middle suffix) =
      atSeparatedVec control target hct leading
        ((UnitaryOperator.controlledQubitsOnZero HOp).applyVec body)
        middle suffix := by
  unfold openControlledHAt
  rw [atSeparatedWires_applyVec, openControlledH_applyVec]

/-- A source-oriented open rotation is literally inactive on its physical
right-control-one branch, with all other tensor fields arbitrary. -/
private theorem openControlledRotYAt_applyVec_atSeparated_controlOne {width : Nat}
    (target control : Fin width) (htc : target.val < control.val) (θ : ℝ)
    (leading : HilbertVector (Qubits target.val))
    (targetState : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits (control.val - target.val - 1)))
    (suffix : HilbertVector (Qubits (width - control.val - 1))) :
    (openControlledRotYAt target control htc θ).applyVec
        (atSeparatedVec target control htc leading
          (HilbertVector.tensor targetState (ket1 : HilbertVector (Qubits 1)))
          middle suffix) =
      atSeparatedVec target control htc leading
        (HilbertVector.tensor targetState (ket1 : HilbertVector (Qubits 1)))
        middle suffix := by
  rw [openControlledRotYAt_applyVec_atSeparated,
    rightControlledQubitsOnZero_applyVec_tensor_ket1]

/-- A leading-control open Hadamard is literally inactive on its physical
left-control-one branch, with all other tensor fields arbitrary. -/
private theorem openControlledHAt_applyVec_atSeparated_controlOne {width : Nat}
    (control target : Fin width) (hct : control.val < target.val)
    (leading : HilbertVector (Qubits control.val))
    (targetState : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits (target.val - control.val - 1)))
    (suffix : HilbertVector (Qubits (width - target.val - 1))) :
    (openControlledHAt control target hct).applyVec
        (atSeparatedVec control target hct leading
          (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) targetState)
          middle suffix) =
      atSeparatedVec control target hct leading
        (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) targetState)
        middle suffix := by
  rw [openControlledHAt_applyVec_atSeparated,
    UnitaryOperator.controlledQubitsOnZero_applyVec_ket1_tensor]

/-- Linearity of an actual circuit over an explicitly finite raw-vector
sum.  It is kept local to make the inactive-control argument below visibly
about the literal circuit matrix. -/
private theorem circuit_applyVec_finset_sum {R : Register} (program : UnitaryCircuit R)
    {α : Type*} (indices : Finset α)
    (term : α → HilbertVector R) :
    program.applyVec (∑ index ∈ indices, term index) =
      ∑ index ∈ indices, program.applyVec (term index) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      have hz := UnitaryCircuit.applyVec_smul program (0 : ℂ) (0 : HilbertVector R)
      simpa using hz
  | @insert index rest fresh induction =>
      rw [Finset.sum_insert fresh, UnitaryCircuit.applyVec_add, induction,
        Finset.sum_insert fresh]

/-- An indexed literal schedule fixes a raw vector when both its stored
prefix and every scheduled member fix that same vector.  This is used for
the already accepted residual blocks; it follows from the actual increasing
`foldl` execution semantics of `indexedProductNamed`. -/
private theorem indexedProductNamed_applyVec_eq_self_of_each {width count : Nat}
    (label : String) (start : UnitaryCircuit (Qubits width))
    (step : Fin count → UnitaryCircuit (Qubits width)) (state : HilbertVector (Qubits width))
    (hstart : start.applyVec state = state)
    (hstep : ∀ index, (step index).applyVec state = state) :
    (UnitaryCircuit.indexedProductNamed label count start step).applyVec state = state := by
  rw [UnitaryCircuit.applyVec_indexedProductNamed, hstart]
  have hfold : ∀ circuits : List (UnitaryCircuit (Qubits width)),
      (∀ circuit ∈ circuits, circuit.applyVec state = state) →
        circuits.foldl (fun accumulated circuit => circuit.applyVec accumulated) state = state := by
    intro circuits
    induction circuits with
    | nil => simp
    | cons circuit circuits induction =>
        intro hcircuits
        rw [List.foldl_cons, hcircuits circuit (by simp)]
        apply induction
        intro later hlater
        exact hcircuits later (by simp [hlater])
  apply hfold (List.ofFn step)
  intro circuit hmember
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hmember
  exact hstep index

/-- An actual right-control open rotation fixes every raw state whose
nonzero basis amplitudes have control component one.  `separatedBasisLabel`
is the concrete physical split, so this does not smuggle in a logical wire
permutation. -/
private theorem openControlledRotYAt_applyVec_eq_self_of_controlOne {width : Nat}
    (target control : Fin width) (htc : target.val < control.val) (θ : ℝ)
    (state : HilbertVector (Qubits width))
    (hsupport : ∀ (leading : Fin (2 ^ target.val)) (first : Fin (2 ^ 1))
      (middle : Fin (2 ^ (control.val - target.val - 1)))
      (second : Fin (2 ^ 1)) (suffix : Fin (2 ^ (width - control.val - 1))),
      state (separatedBasisLabel target control htc leading first middle second suffix) ≠ 0 →
        second = 1) :
    (openControlledRotYAt target control htc θ).applyVec state = state := by
  classical
  have hsum :
      state = ∑ index : Fin (2 ^ width),
        state index •
          (NormalizedVector.ket (R := Qubits width) index :
            HilbertVector (Qubits width)) :=
    (HilbertVector.sum_amplitude_smul_ket state).symm
  calc
    (openControlledRotYAt target control htc θ).applyVec state =
          (openControlledRotYAt target control htc θ).applyVec
          (∑ index : Fin (2 ^ width),
            state index •
              (NormalizedVector.ket (R := Qubits width) index :
                HilbertVector (Qubits width))) := by
          exact congrArg
            (fun vector : HilbertVector (Qubits width) =>
              (openControlledRotYAt target control htc θ).applyVec vector)
            hsum
    _ = ∑ index : Fin (2 ^ width),
          (openControlledRotYAt target control htc θ).applyVec
            (state index •
              (NormalizedVector.ket (R := Qubits width) index :
                HilbertVector (Qubits width))) := by
          exact circuit_applyVec_finset_sum
            (openControlledRotYAt target control htc θ) Finset.univ
            (fun index => state index •
              (NormalizedVector.ket (R := Qubits width) index :
                HilbertVector (Qubits width)))
    _ = ∑ index : Fin (2 ^ width), state index •
          (openControlledRotYAt target control htc θ).applyVec
            (NormalizedVector.ket (R := Qubits width) index :
              HilbertVector (Qubits width)) := by
          apply Finset.sum_congr rfl
          intro index _
          rw [UnitaryCircuit.applyVec_smul]
    _ = ∑ index : Fin (2 ^ width), state index •
          (NormalizedVector.ket (R := Qubits width) index :
            HilbertVector (Qubits width)) := by
          apply Finset.sum_congr rfl
          intro index _
          obtain ⟨leading, first, middle, second, suffix, hindex⟩ :=
            exists_separatedBasisLabel target control htc index
          rw [← hindex]
          by_cases hzero : state
              (separatedBasisLabel target control htc leading first middle second suffix) = 0
          · simp [hzero]
          · have hsecond := hsupport leading first middle second suffix hzero
            subst second
            have hinactive :
                (openControlledRotYAt target control htc θ).applyVec
                    (NormalizedVector.ket (R := Qubits width)
                      (separatedBasisLabel target control htc leading first middle 1 suffix) :
                      HilbertVector (Qubits width)) =
                  (NormalizedVector.ket (R := Qubits width)
                    (separatedBasisLabel target control htc leading first middle 1 suffix) :
                    HilbertVector (Qubits width)) := by
              have hket := atSeparatedVec_tensor_ket target control htc
                leading first middle (1 : Fin (2 ^ 1)) suffix
              have hket' :
                  atSeparatedVec target control htc
                      (NormalizedVector.ket (R := Qubits target.val) leading :
                        HilbertVector (Qubits target.val))
                      (HilbertVector.tensor
                        (NormalizedVector.ket (R := Qubits 1) first :
                          HilbertVector (Qubits 1))
                        (ket1 : HilbertVector (Qubits 1)))
                      (NormalizedVector.ket
                        (R := Qubits (control.val - target.val - 1)) middle :
                        HilbertVector (Qubits (control.val - target.val - 1)))
                      (NormalizedVector.ket
                        (R := Qubits (width - control.val - 1)) suffix :
                        HilbertVector (Qubits (width - control.val - 1))) =
                    (NormalizedVector.ket (R := Qubits width)
                      (separatedBasisLabel target control htc
                        leading first middle 1 suffix) :
                      HilbertVector (Qubits width)) := by
                simpa only [basisKetVec, ket1] using hket
              calc
                _ = (openControlledRotYAt target control htc θ).applyVec
                    (atSeparatedVec target control htc
                      (NormalizedVector.ket (R := Qubits target.val) leading :
                        HilbertVector (Qubits target.val))
                      (HilbertVector.tensor
                        (NormalizedVector.ket (R := Qubits 1) first :
                          HilbertVector (Qubits 1))
                        (ket1 : HilbertVector (Qubits 1)))
                      (NormalizedVector.ket
                        (R := Qubits (control.val - target.val - 1)) middle :
                        HilbertVector (Qubits (control.val - target.val - 1)))
                      (NormalizedVector.ket
                        (R := Qubits (width - control.val - 1)) suffix :
                        HilbertVector (Qubits (width - control.val - 1)))) := by
                      exact congrArg
                        (openControlledRotYAt target control htc θ).applyVec
                        hket'.symm
                _ = atSeparatedVec target control htc
                      (NormalizedVector.ket (R := Qubits target.val) leading :
                        HilbertVector (Qubits target.val))
                      (HilbertVector.tensor
                        (NormalizedVector.ket (R := Qubits 1) first :
                          HilbertVector (Qubits 1))
                        (ket1 : HilbertVector (Qubits 1)))
                      (NormalizedVector.ket
                        (R := Qubits (control.val - target.val - 1)) middle :
                        HilbertVector (Qubits (control.val - target.val - 1)))
                      (NormalizedVector.ket
                        (R := Qubits (width - control.val - 1)) suffix :
                        HilbertVector (Qubits (width - control.val - 1))) :=
                      openControlledRotYAt_applyVec_atSeparated_controlOne
                        target control htc θ _ _ _ _
                _ = _ := hket'
            exact congrArg
              (fun vector : HilbertVector (Qubits width) =>
                state
                  (separatedBasisLabel target control htc leading first middle 1 suffix) • vector)
              hinactive
    _ = state := HilbertVector.sum_amplitude_smul_ket state

/-- The corresponding raw support statement for the literal leading-control
open Hadamard. -/
private theorem openControlledHAt_applyVec_eq_self_of_controlOne {width : Nat}
    (control target : Fin width) (hct : control.val < target.val)
    (state : HilbertVector (Qubits width))
    (hsupport : ∀ (leading : Fin (2 ^ control.val)) (first : Fin (2 ^ 1))
      (middle : Fin (2 ^ (target.val - control.val - 1)))
      (second : Fin (2 ^ 1)) (suffix : Fin (2 ^ (width - target.val - 1))),
      state (separatedBasisLabel control target hct leading first middle second suffix) ≠ 0 →
        first = 1) :
    (openControlledHAt control target hct).applyVec state = state := by
  classical
  have hsum :
      state = ∑ index : Fin (2 ^ width),
        state index •
          (NormalizedVector.ket (R := Qubits width) index :
            HilbertVector (Qubits width)) :=
    (HilbertVector.sum_amplitude_smul_ket state).symm
  calc
    (openControlledHAt control target hct).applyVec state =
          (openControlledHAt control target hct).applyVec
          (∑ index : Fin (2 ^ width),
            state index •
              (NormalizedVector.ket (R := Qubits width) index :
                HilbertVector (Qubits width))) := by
          exact congrArg
            (fun vector : HilbertVector (Qubits width) =>
              (openControlledHAt control target hct).applyVec vector)
            hsum
    _ = ∑ index : Fin (2 ^ width),
          (openControlledHAt control target hct).applyVec
            (state index •
              (NormalizedVector.ket (R := Qubits width) index :
                HilbertVector (Qubits width))) := by
          exact circuit_applyVec_finset_sum
            (openControlledHAt control target hct) Finset.univ
            (fun index => state index •
              (NormalizedVector.ket (R := Qubits width) index :
                HilbertVector (Qubits width)))
    _ = ∑ index : Fin (2 ^ width), state index •
          (openControlledHAt control target hct).applyVec
            (NormalizedVector.ket (R := Qubits width) index :
              HilbertVector (Qubits width)) := by
          apply Finset.sum_congr rfl
          intro index _
          rw [UnitaryCircuit.applyVec_smul]
    _ = ∑ index : Fin (2 ^ width), state index •
          (NormalizedVector.ket (R := Qubits width) index :
            HilbertVector (Qubits width)) := by
          apply Finset.sum_congr rfl
          intro index _
          obtain ⟨leading, first, middle, second, suffix, hindex⟩ :=
            exists_separatedBasisLabel control target hct index
          rw [← hindex]
          by_cases hzero : state
              (separatedBasisLabel control target hct leading first middle second suffix) = 0
          · simp [hzero]
          · have hfirst := hsupport leading first middle second suffix hzero
            subst first
            have hinactive :
                (openControlledHAt control target hct).applyVec
                    (NormalizedVector.ket (R := Qubits width)
                      (separatedBasisLabel control target hct leading 1 middle second suffix) :
                      HilbertVector (Qubits width)) =
                  (NormalizedVector.ket (R := Qubits width)
                    (separatedBasisLabel control target hct leading 1 middle second suffix) :
                    HilbertVector (Qubits width)) := by
              have hket := atSeparatedVec_tensor_ket control target hct
                leading (1 : Fin (2 ^ 1)) middle second suffix
              have hket' :
                  atSeparatedVec control target hct
                      (NormalizedVector.ket (R := Qubits control.val) leading :
                        HilbertVector (Qubits control.val))
                      (HilbertVector.tensor
                        (ket1 : HilbertVector (Qubits 1))
                        (NormalizedVector.ket (R := Qubits 1) second :
                          HilbertVector (Qubits 1)))
                      (NormalizedVector.ket
                        (R := Qubits (target.val - control.val - 1)) middle :
                        HilbertVector (Qubits (target.val - control.val - 1)))
                      (NormalizedVector.ket
                        (R := Qubits (width - target.val - 1)) suffix :
                        HilbertVector (Qubits (width - target.val - 1))) =
                    (NormalizedVector.ket (R := Qubits width)
                      (separatedBasisLabel control target hct
                        leading 1 middle second suffix) :
                      HilbertVector (Qubits width)) := by
                simpa only [basisKetVec, ket1] using hket
              calc
                _ = (openControlledHAt control target hct).applyVec
                    (atSeparatedVec control target hct
                      (NormalizedVector.ket (R := Qubits control.val) leading :
                        HilbertVector (Qubits control.val))
                      (HilbertVector.tensor
                        (ket1 : HilbertVector (Qubits 1))
                        (NormalizedVector.ket (R := Qubits 1) second :
                          HilbertVector (Qubits 1)))
                      (NormalizedVector.ket
                        (R := Qubits (target.val - control.val - 1)) middle :
                        HilbertVector (Qubits (target.val - control.val - 1)))
                      (NormalizedVector.ket
                        (R := Qubits (width - target.val - 1)) suffix :
                        HilbertVector (Qubits (width - target.val - 1)))) := by
                      exact congrArg
                        (openControlledHAt control target hct).applyVec hket'.symm
                _ = atSeparatedVec control target hct
                      (NormalizedVector.ket (R := Qubits control.val) leading :
                        HilbertVector (Qubits control.val))
                      (HilbertVector.tensor
                        (ket1 : HilbertVector (Qubits 1))
                        (NormalizedVector.ket (R := Qubits 1) second :
                          HilbertVector (Qubits 1)))
                      (NormalizedVector.ket
                        (R := Qubits (target.val - control.val - 1)) middle :
                        HilbertVector (Qubits (target.val - control.val - 1)))
                      (NormalizedVector.ket
                        (R := Qubits (width - target.val - 1)) suffix :
                        HilbertVector (Qubits (width - target.val - 1))) :=
                      openControlledHAt_applyVec_atSeparated_controlOne
                        control target hct _ _ _ _
                _ = _ := hket'
            exact congrArg
              (fun vector : HilbertVector (Qubits width) =>
                state
                  (separatedBasisLabel control target hct leading 1 middle second suffix) • vector)
              hinactive
    _ = state := HilbertVector.sum_amplitude_smul_ket state

/-- A one-qubit computational label is one as soon as its only bit reads
true. -/
private theorem oneQubitLabel_eq_one_of_testBit_true (bit : Fin (2 ^ 1))
    (hbit : bit.val.testBit 0 = true) : bit = 1 := by
  fin_cases bit <;> simp_all

namespace BinaryExpansion

variable {N : Nat}

/-- A later source rotation is literally inactive on every already accepted
residual block.  The proof passes through the concrete five-field physical
split, then uses the binary interval arithmetic to identify its right
control field as one. -/
private theorem residualBlock_openControlledRotYAt_applyVec_eq_self
    (b : BinaryExpansion N) (gap : Fin b.s)
    {accepted : Fin (b.s + 1)} (haccepted : accepted.val < gap.castSucc.val) :
    (openControlledRotYAt (b.wire gap.succ) (b.wire gap.castSucc)
      (b.wire_succ_lt_wire gap) (b.sourceAngle gap)).applyVec
        (b.residualBlock accepted) = b.residualBlock accepted := by
  apply openControlledRotYAt_applyVec_eq_self_of_controlOne
  intro leading first middle second suffix hnonzero
  have hsupport : b.residualSupport accepted
      (separatedBasisLabel (b.wire gap.succ) (b.wire gap.castSucc)
        (b.wire_succ_lt_wire gap) leading first middle second suffix).val := by
    by_contra hnot
    exact hnonzero (b.residualBlock_apply_of_not_support accepted _ hnot)
  have hbit := b.residualSupport_testBit_true_of_lt haccepted hsupport
  have hcontrol :
      (separatedBasisLabel (b.wire gap.succ) (b.wire gap.castSucc)
        (b.wire_succ_lt_wire gap) leading first middle second suffix).val.testBit
          (WireAddress.bitIndex (b.wire gap.castSucc)).val = true := by
    rw [b.bitIndex_wire gap.castSucc]
    exact hbit
  rw [separatedBasisLabel_testBit_second] at hcontrol
  exact oneQubitLabel_eq_one_of_testBit_true second hcontrol

/-- A gap Hadamard is literally inactive on every residual block accepted at
or below that gap.  Its physical left control is the next source bit. -/
private theorem residualBlock_openControlledHAt_applyVec_eq_self
    (b : BinaryExpansion N) (gap : Fin b.s)
    (offset : Fin (b.ell gap.succ - b.ell gap.castSucc))
    {accepted : Fin (b.s + 1)} (haccepted : accepted.val < gap.succ.val) :
    (openControlledHAt (b.wire gap.succ) (b.gapTargetWire gap offset)
      (b.wire_succ_lt_gapTargetWire gap offset)).applyVec
        (b.residualBlock accepted) = b.residualBlock accepted := by
  apply openControlledHAt_applyVec_eq_self_of_controlOne
  intro leading first middle second suffix hnonzero
  have hsupport : b.residualSupport accepted
      (separatedBasisLabel (b.wire gap.succ) (b.gapTargetWire gap offset)
        (b.wire_succ_lt_gapTargetWire gap offset) leading first middle second suffix).val := by
    by_contra hnot
    exact hnonzero (b.residualBlock_apply_of_not_support accepted _ hnot)
  have hbit := b.residualSupport_testBit_true_of_lt haccepted hsupport
  have hcontrol :
      (separatedBasisLabel (b.wire gap.succ) (b.gapTargetWire gap offset)
        (b.wire_succ_lt_gapTargetWire gap offset) leading first middle second suffix).val.testBit
          (WireAddress.bitIndex (b.wire gap.succ)).val = true := by
    rw [b.bitIndex_wire gap.succ]
    exact hbit
  rw [separatedBasisLabel_testBit_first] at hcontrol
  exact oneQubitLabel_eq_one_of_testBit_true first hcontrol

/-- The literal indexed H layer is inactive on every already accepted block.
This is an action theorem about its actual increasing `indexedProductNamed`
tree, obtained by folding the concrete per-offset lowering. -/
private theorem gapHadamardLayer_applyVec_residualBlock_eq_self
    (b : BinaryExpansion N) (gap : Fin b.s)
    {accepted : Fin (b.s + 1)} (haccepted : accepted.val < gap.succ.val) :
    (b.gapHadamardLayer gap).applyVec (b.residualBlock accepted) =
      b.residualBlock accepted := by
  unfold gapHadamardLayer
  apply indexedProductNamed_applyVec_eq_self_of_each
  · rw [idleCircuit, UnitaryCircuit.applyVec_identity]
  · intro offset
    exact b.residualBlock_openControlledHAt_applyVec_eq_self gap offset haccepted

/-- The aligned residual before a source rotation, expressed with the
physical rotation target isolated at its literal wire.  This is a tensor
layout identity derived from `residualBlock_gap_rotation_tensor`; its two
casts only reconcile source arithmetic with the addressed `atWire` widths. -/
private theorem residualBlock_eq_rotYAtWireTensor
    (b : BinaryExpansion N) (gap : Fin b.s) :
    b.residualBlock gap.castSucc =
      castWidthVec (by omega :
        (b.wire gap.succ).val + 1 +
            (b.width - (b.wire gap.succ).val - 1) = b.width)
        (HilbertVector.tensor
          (HilbertVector.tensor
            (castWidthVec (by
              rw [b.wire_val gap.succ]
              have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
              omega : b.width - b.ell gap.succ - 1 =
                (b.wire gap.succ).val)
              (basisKetVec (b.residualHighLabel gap.succ)))
            (ket1 : HilbertVector (Qubits 1)))
          (castWidthVec (by
            rw [b.wire_val gap.succ]
            have hsource : b.ell gap.castSucc < b.ell gap.succ :=
              b.ell_strict gap.castSucc_lt_succ
            have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
            unfold gapWidth
            omega : (b.gapWidth gap - 1) +
                (1 + b.ell gap.castSucc) =
              b.width - (b.wire gap.succ).val - 1)
            (HilbertVector.tensor
              (rawKetZero (b.gapWidth gap - 1))
              (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
                (WalshHadamard.uniformState (b.ell gap.castSucc) :
                  HilbertVector (Qubits (b.ell gap.castSucc))))))) := by
  have hsource : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  have hgapPositive : 0 < b.gapWidth gap := by
    unfold gapWidth
    omega
  let high := (basisKetVec (b.residualHighLabel gap.succ))
  let middle := rawKetZero (b.gapWidth gap - 1)
  let suffix := (WalshHadamard.uniformState (b.ell gap.castSucc) :
    HilbertVector (Qubits (b.ell gap.castSucc)))
  have horiginal :
      ((b.width - b.ell gap.succ - 1) +
          (1 + (b.gapWidth gap - 1))) +
          (1 + b.ell gap.castSucc) = b.width := by
    unfold gapWidth
    omega
  have hcanonical :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) = b.width := by
    unfold gapWidth
    omega
  have hfirstAssoc :
      ((b.width - b.ell gap.succ - 1) +
          (1 + (b.gapWidth gap - 1))) +
          (1 + b.ell gap.castSucc) =
        (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) := by
    omega
  have hrawAssoc :
      ((b.width - b.ell gap.succ - 1) + 1) +
          ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc)) =
        (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) := by
    omega
  have hleft : b.width - b.ell gap.succ - 1 =
      (b.wire gap.succ).val := by
    rw [b.wire_val gap.succ]
    omega
  have hright : (b.gapWidth gap - 1) +
      (1 + b.ell gap.castSucc) =
      b.width - (b.wire gap.succ).val - 1 := by
    rw [b.wire_val gap.succ]
    unfold gapWidth
    omega
  have hwhole : (b.wire gap.succ).val + 1 +
      (b.width - (b.wire gap.succ).val - 1) = b.width := by
    omega
  calc
    b.residualBlock gap.castSucc =
        castWidthVec horiginal
          (HilbertVector.tensor
            (HilbertVector.tensor high
              (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) middle))
            (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix)) := by
          simpa [high, middle, suffix] using
            b.residualBlock_gap_rotation_tensor gap
    _ = castWidthVec hcanonical
          (castWidthVec hfirstAssoc
            (HilbertVector.tensor
              (HilbertVector.tensor high
                (HilbertVector.tensor (ket1 : HilbertVector (Qubits 1)) middle))
              (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix))) := by
          rw [castWidthVec_trans]
    _ = castWidthVec hcanonical
          (castWidthVec hrawAssoc
            (HilbertVector.tensor
              (HilbertVector.tensor high (ket1 : HilbertVector (Qubits 1)))
              (HilbertVector.tensor middle
                (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix)))) := by
          congr 1
          simpa using raw_tensor_rotation5 high
            (ket1 : HilbertVector (Qubits 1)) middle
            (ket0 : HilbertVector (Qubits 1)) suffix
    _ = castWidthVec (hrawAssoc.trans hcanonical)
          (HilbertVector.tensor
            (HilbertVector.tensor high (ket1 : HilbertVector (Qubits 1)))
            (HilbertVector.tensor middle
              (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix))) := by
          rw [castWidthVec_trans]
    _ = castWidthVec hwhole
          (HilbertVector.tensor
            (HilbertVector.tensor (castWidthVec hleft high)
              (ket1 : HilbertVector (Qubits 1)))
            (castWidthVec hright
              (HilbertVector.tensor middle
                (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix)))) := by
          simpa using
            (raw_tensor_rotation5_transport hleft hright
              (hrawAssoc.trans hcanonical) hwhole high
              (ket1 : HilbertVector (Qubits 1)) middle
              (ket0 : HilbertVector (Qubits 1)) suffix)

/-- The new zero branch of a source rotation, in the same target-isolated
physical tensor layout.  It is the corresponding layout theorem for
`gapHPartial gap 0`, so the uncontrolled first rotation and later
right-control rotations share the same concrete branch state. -/
private theorem gapHPartial_zero_eq_rotYAtWireTensor
    (b : BinaryExpansion N) (gap : Fin b.s) :
    b.gapHPartial gap 0 (Nat.zero_le _) =
      castWidthVec (by omega :
        (b.wire gap.succ).val + 1 +
            (b.width - (b.wire gap.succ).val - 1) = b.width)
        (HilbertVector.tensor
          (HilbertVector.tensor
            (castWidthVec (by
              rw [b.wire_val gap.succ]
              have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
              omega : b.width - b.ell gap.succ - 1 =
                (b.wire gap.succ).val)
              (basisKetVec (b.residualHighLabel gap.succ)))
            (ket0 : HilbertVector (Qubits 1)))
          (castWidthVec (by
            rw [b.wire_val gap.succ]
            have hsource : b.ell gap.castSucc < b.ell gap.succ :=
              b.ell_strict gap.castSucc_lt_succ
            have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
            unfold gapWidth
            omega : (b.gapWidth gap - 1) +
                (1 + b.ell gap.castSucc) =
              b.width - (b.wire gap.succ).val - 1)
            (HilbertVector.tensor
              (rawKetZero (b.gapWidth gap - 1))
              (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
                (WalshHadamard.uniformState (b.ell gap.castSucc) :
                  HilbertVector (Qubits (b.ell gap.castSucc))))))) := by
  have hsource : b.ell gap.castSucc < b.ell gap.succ :=
    b.ell_strict gap.castSucc_lt_succ
  have hwidth : b.ell gap.succ < b.width := b.ell_lt_width gap.succ
  have hpositive : 0 < b.gapWidth gap := by
    unfold gapWidth
    omega
  let high := (basisKetVec (b.residualHighLabel gap.succ))
  let middle := rawKetZero (b.gapWidth gap - 1)
  let suffix := (WalshHadamard.uniformState (b.ell gap.castSucc) :
    HilbertVector (Qubits (b.ell gap.castSucc)))
  let innerSource := HilbertVector.tensor
    (ket0 : HilbertVector (Qubits 1))
    (HilbertVector.tensor (gapPlusBlock 0) suffix)
  have hinnerWidth :
      1 + (0 + b.ell gap.castSucc) = 1 + b.ell gap.castSucc := by
    omega
  have hzeroTail :
      castWidthVec (Nat.zero_add (b.ell gap.castSucc))
          (HilbertVector.tensor (gapPlusBlock 0) suffix) = suffix := by
    change castWidthVec (Nat.zero_add (b.ell gap.castSucc))
        (HilbertVector.tensor (rawKetZero 0) suffix) = suffix
    exact raw_ket0_tensor_left_zero suffix
  have hinnerState :
      castWidthVec hinnerWidth innerSource =
        HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix := by
    unfold innerSource
    calc
      castWidthVec hinnerWidth
          (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
            (HilbertVector.tensor (gapPlusBlock 0) suffix)) =
          castWidthVec rfl
            (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              (castWidthVec (Nat.zero_add (b.ell gap.castSucc))
                (HilbertVector.tensor (gapPlusBlock 0) suffix))) := by
            symm
            simpa using
              (castWidthVec_tensor_right_transport
                (Nat.zero_add (b.ell gap.castSucc)) rfl
                (ket0 : HilbertVector (Qubits 1))
                (HilbertVector.tensor (gapPlusBlock 0) suffix))
      _ = _ := by rw [hzeroTail, castWidthVec_self]
  have hsourceCanonical :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + (0 + b.ell gap.castSucc)))) = b.width := by
    unfold gapWidth
    omega
  have hcanonical :
      (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) = b.width := by
    unfold gapWidth
    omega
  have hrawAssoc :
      ((b.width - b.ell gap.succ - 1) + 1) +
          ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc)) =
        (b.width - b.ell gap.succ - 1) +
          (1 + ((b.gapWidth gap - 1) +
            (1 + b.ell gap.castSucc))) := by
    omega
  have hleft : b.width - b.ell gap.succ - 1 =
      (b.wire gap.succ).val := by
    rw [b.wire_val gap.succ]
    omega
  have hright : (b.gapWidth gap - 1) +
      (1 + b.ell gap.castSucc) =
      b.width - (b.wire gap.succ).val - 1 := by
    rw [b.wire_val gap.succ]
    unfold gapWidth
    omega
  have hwhole : (b.wire gap.succ).val + 1 +
      (b.width - (b.wire gap.succ).val - 1) = b.width := by
    omega
  calc
    b.gapHPartial gap 0 (Nat.zero_le _) =
        castWidthVec hsourceCanonical
          (HilbertVector.tensor high
            (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              (HilbertVector.tensor middle
                innerSource))) := by
          simpa [high, middle, suffix, innerSource] using
            b.gapHPartial_canonical gap 0 hpositive
    _ = castWidthVec hcanonical
          (HilbertVector.tensor high
            (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1))
              (HilbertVector.tensor middle
                (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix)))) := by
          rw [castWidthVec_tensor_three_right_transport
            hinnerWidth hsourceCanonical hcanonical]
          rw [hinnerState]
    _ = castWidthVec hcanonical
          (castWidthVec hrawAssoc
            (HilbertVector.tensor
              (HilbertVector.tensor high (ket0 : HilbertVector (Qubits 1)))
              (HilbertVector.tensor middle
                (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix)))) := by
          congr 1
          simpa using raw_tensor_right_to_rotation5 high
            (ket0 : HilbertVector (Qubits 1)) middle
            (ket0 : HilbertVector (Qubits 1)) suffix
    _ = castWidthVec (hrawAssoc.trans hcanonical)
          (HilbertVector.tensor
            (HilbertVector.tensor high (ket0 : HilbertVector (Qubits 1)))
            (HilbertVector.tensor middle
              (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix))) := by
          rw [castWidthVec_trans]
    _ = castWidthVec hwhole
          (HilbertVector.tensor
            (HilbertVector.tensor (castWidthVec hleft high)
              (ket0 : HilbertVector (Qubits 1)))
            (castWidthVec hright
              (HilbertVector.tensor middle
                (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) suffix)))) := by
          simpa using
            (raw_tensor_rotation5_transport hleft hright
              (hrawAssoc.trans hcanonical) hwhole high
              (ket0 : HilbertVector (Qubits 1)) middle
              (ket0 : HilbertVector (Qubits 1)) suffix)

/-- The first source rotation is the same literal addressed `R_Y` circuit as
the schedule specifies.  On the current aligned residual it creates the
zero branch and retains the one branch with the same signed coefficients as
the later right-control lowering. -/
private theorem rotYAtWire_applyVec_residualBlock_active
    (b : BinaryExpansion N) (gap : Fin b.s) :
    (rotYAtWire (b.wire gap.succ) (b.sourceAngle gap)).applyVec
        (b.residualBlock gap.castSucc) =
      (-(Real.sin (b.sourceAngle gap / 2)) : ℂ) •
          b.gapHPartial gap 0 (Nat.zero_le _) +
        (Real.cos (b.sourceAngle gap / 2) : ℂ) •
          b.residualBlock gap.castSucc := by
  rw [b.residualBlock_eq_rotYAtWireTensor gap]
  rw [rotYAtWire_applyVec_tensor_ket1]
  rw [← b.gapHPartial_zero_eq_rotYAtWireTensor gap,
    ← b.residualBlock_eq_rotYAtWireTensor gap]

/-- One literal addressed gap-H lowering advances the raw residual branch by
exactly one processed target.  Its body action is the proved operator action
of the decomposed `openControlledH`, not a schematic controlled gate.  This
appears after the lowering's raw-vector semantics so the proof uses the
literal circuit equation rather than a forward declaration. -/
private theorem openControlledHAt_applyVec_gapHPartial
    (b : BinaryExpansion N) (gap : Fin b.s) (processed : Nat)
    (hprocessed : processed < b.gapWidth gap) :
    (openControlledHAt (b.wire gap.succ)
      (b.gapTargetWire gap ⟨processed, hprocessed⟩)
      (b.wire_succ_lt_gapTargetWire gap ⟨processed, hprocessed⟩)).applyVec
        (b.gapHPartial gap processed (Nat.le_of_lt hprocessed)) =
      b.gapHPartial gap (processed + 1) (Nat.succ_le_of_lt hprocessed) := by
  rw [b.gapHPartial_eq_hSeparated gap processed hprocessed]
  rw [openControlledHAt_applyVec_atSeparated,
    UnitaryOperator.controlledQubitsOnZero_applyVec_ket0_tensor,
    HOp_applyVec_ket0]
  exact (b.gapHPartial_succ_eq_hSeparatedPlus gap processed hprocessed).symm

/-- The literal right-control open rotation splits the current residual into
its newly active zero branch and retained one branch with the signed
`R_Y` coefficients fixed by the proved lowering semantics. -/
private theorem openControlledRotYAt_applyVec_residualBlock_active
    (b : BinaryExpansion N) (gap : Fin b.s) :
    (openControlledRotYAt (b.wire gap.succ) (b.wire gap.castSucc)
      (b.wire_succ_lt_wire gap) (b.sourceAngle gap)).applyVec
        (b.residualBlock gap.castSucc) =
      (-(Real.sin (b.sourceAngle gap / 2)) : ℂ) •
          b.gapHPartial gap 0 (Nat.zero_le _) +
        (Real.cos (b.sourceAngle gap / 2) : ℂ) •
          b.residualBlock gap.castSucc := by
  rw [b.residualBlock_eq_rotationSeparated gap]
  rw [openControlledRotYAt_applyVec_atSeparated,
    rightControlledQubitsOnZero_applyVec_tensor_ket0,
    rotYOp_applyVec_ket1, HilbertVector.add_tensor,
    HilbertVector.smul_tensor, HilbertVector.smul_tensor]
  rw [atSeparatedVec_add_body, atSeparatedVec_smul_body,
    atSeparatedVec_smul_body]
  rw [← b.gapHPartial_zero_eq_rotationSeparated gap,
    ← b.residualBlock_eq_rotationSeparated gap]

/-- The increasing `List.ofFn` prefix of literal gap-H lowerings advances
the raw partial state by its prefix length.  This follows the concrete
`foldl` execution order used by `UnitaryCircuit.indexedProductNamed`. -/
private theorem gapHPartial_foldl_applyVec (b : BinaryExpansion N)
    (gap : Fin b.s) :
    ∀ (count : Nat) (hcount : count ≤ b.gapWidth gap),
      (List.ofFn (fun index : Fin count =>
        openControlledHAt (b.wire gap.succ)
          (b.gapTargetWire gap (Fin.castLE hcount index))
          (b.wire_succ_lt_gapTargetWire gap (Fin.castLE hcount index)))).foldl
          (fun state circuit => circuit.applyVec state)
          (b.gapHPartial gap 0 (Nat.zero_le _)) =
        b.gapHPartial gap count hcount := by
  intro count
  induction count with
  | zero =>
      intro _
      simp
  | succ count induction =>
      intro hcount
      have hprev : count ≤ b.gapWidth gap := Nat.le_of_succ_le hcount
      have hstep : count < b.gapWidth gap := by
        omega
      have hprefix :
          (List.ofFn (fun index : Fin count =>
            openControlledHAt (b.wire gap.succ)
              (b.gapTargetWire gap (Fin.castLE hcount index.castSucc))
              (b.wire_succ_lt_gapTargetWire gap
                (Fin.castLE hcount index.castSucc)))).foldl
              (fun state circuit => circuit.applyVec state)
              (b.gapHPartial gap 0 (Nat.zero_le _)) =
            b.gapHPartial gap count hprev := by
          simpa using induction hprev
      have hlast : Fin.castLE hcount (Fin.last count) =
          (⟨count, hstep⟩ : Fin (b.gapWidth gap)) := by
        apply Fin.ext
        rfl
      rw [List.ofFn_succ', List.concat_eq_append, List.foldl_concat,
        hprefix, hlast]
      simpa using b.openControlledHAt_applyVec_gapHPartial gap count hstep

/-- The actual indexed H layer maps the newly opened zero branch through all
of its literal target lowerings.  The result is stated as the final raw
partial state so the following residual equation can identify it with the
next aligned block. -/
private theorem gapHadamardLayer_applyVec_gapHPartial_zero
    (b : BinaryExpansion N) (gap : Fin b.s) :
    (b.gapHadamardLayer gap).applyVec
        (b.gapHPartial gap 0 (Nat.zero_le _)) =
      b.gapHPartial gap (b.gapWidth gap) (Nat.le_refl _) := by
  unfold gapHadamardLayer
  rw [UnitaryCircuit.applyVec_indexedProductNamed, idleCircuit, UnitaryCircuit.applyVec_identity]
  exact b.gapHPartial_foldl_applyVec gap (b.gapWidth gap) (Nat.le_refl _)

/-- The literal indexed H layer turns its active zero branch into the next
aligned residual block. -/
private theorem gapHadamardLayer_applyVec_active_branch
    (b : BinaryExpansion N) (gap : Fin b.s) :
    (b.gapHadamardLayer gap).applyVec
        (b.gapHPartial gap 0 (Nat.zero_le _)) =
      b.residualBlock gap.succ := by
  rw [b.gapHadamardLayer_applyVec_gapHPartial_zero]
  exact b.gapHPartial_final_eq_residualBlock gap

/-- One literal Algorithm-1 gap stage performs its proved rotation split and
then runs the same literal indexed H layer on the newly open branch.  The
already retained residual is fixed by that H layer's physical high control. -/
private theorem gapStage_applyVec_residualBlock_active
    (b : BinaryExpansion N) (gap : Fin b.s) :
    (b.gapStage gap).applyVec (b.residualBlock gap.castSucc) =
      (-(Real.sin (b.sourceAngle gap / 2)) : ℂ) • b.residualBlock gap.succ +
        (Real.cos (b.sourceAngle gap / 2) : ℂ) • b.residualBlock gap.castSucc := by
  have hinactive :
      (b.gapHadamardLayer gap).applyVec (b.residualBlock gap.castSucc) =
        b.residualBlock gap.castSucc :=
    b.gapHadamardLayer_applyVec_residualBlock_eq_self gap
      (accepted := gap.castSucc) (by simp)
  unfold gapStage
  split_ifs with hfirst
  · rw [UnitaryCircuit.applyVec_seq,
      b.rotYAtWire_applyVec_residualBlock_active gap,
      UnitaryCircuit.applyVec_add, UnitaryCircuit.applyVec_smul, UnitaryCircuit.applyVec_smul,
      b.gapHadamardLayer_applyVec_active_branch, hinactive]
  · rw [UnitaryCircuit.applyVec_seq,
      b.openControlledRotYAt_applyVec_residualBlock_active gap,
      UnitaryCircuit.applyVec_add, UnitaryCircuit.applyVec_smul, UnitaryCircuit.applyVec_smul,
      b.gapHadamardLayer_applyVec_active_branch, hinactive]

/-- Every later literal stage fixes an already accepted residual block.  At
the first stage this hypothesis is empty; afterwards the rotation and every
H lowering are both inactive by their concrete physical controls. -/
private theorem gapStage_applyVec_residualBlock_eq_self
    (b : BinaryExpansion N) (gap : Fin b.s)
    {accepted : Fin (b.s + 1)} (haccepted : accepted.val < gap.castSucc.val) :
    (b.gapStage gap).applyVec (b.residualBlock accepted) =
      b.residualBlock accepted := by
  unfold gapStage
  split_ifs with hfirst
  · exfalso
    have hzero : gap.castSucc.val = 0 := by
      simpa using hfirst
    omega
  · rw [UnitaryCircuit.applyVec_seq,
      b.residualBlock_openControlledRotYAt_applyVec_eq_self gap haccepted,
      b.gapHadamardLayer_applyVec_residualBlock_eq_self gap
        (lt_trans haccepted (by simp))]

/- The next two lemmas identify the literal initial X/H prefix with the
zeroth aligned residual.  They live after the raw lowering semantics so the
later cross-gap fold has one contiguous matrix-action proof block. -/

/-- The literal X prefix address is the concrete product label consisting of
the residual high prefix, its zero source bit, and the all-zero low suffix. -/
private theorem initialXLabel_eq_tensorLabel (b : BinaryExpansion N) :
    b.initialXLabel =
      castWidthIndex (by
        have hle : b.first ≤ b.last :=
          b.ell_strict.monotone (Fin.zero_le _)
        unfold width
        omega : (b.width - b.first) + b.first = b.width)
        (prodEquiv (m := b.width - b.first) (n := b.first)
          (castWidthIndex (by
            have hfirst := b.first_lt_width
            omega :
            (b.width - b.first - 1) + 1 = b.width - b.first)
            (prodEquiv (m := b.width - b.first - 1) (n := 1)
              (b.residualHighLabel 0, 0)), 0)) := by
  apply Fin.ext
  rw [b.initialXLabel_val,
    b.tailMass_eq_residualHigh_mul (0 : Fin (b.s + 1))]
  simp only [castWidthIndex_val, prodEquiv_val, residualHighLabel_val]
  unfold first
  rw [pow_succ]
  simp [mul_assoc]

/-- Raw-vector form of the preceding concrete initial address split. -/
private theorem initialXLabel_raw_tensor (b : BinaryExpansion N) :
    (NormalizedVector.ket (R := Qubits b.width) b.initialXLabel :
      HilbertVector (Qubits b.width)) =
      castWidthVec (by
        have hle : b.first ≤ b.last :=
          b.ell_strict.monotone (Fin.zero_le _)
        unfold width
        omega : (b.width - b.first) + b.first = b.width)
        (HilbertVector.tensor
          (castWidthVec (by
            have hfirst := b.first_lt_width
            omega :
            (b.width - b.first - 1) + 1 = b.width - b.first)
            (HilbertVector.tensor
              (basisKetVec (b.residualHighLabel 0))
              (ket0 : HilbertVector (Qubits 1))))
          (rawKetZero b.first)) := by
  change basisKetVec b.initialXLabel = _
  rw [b.initialXLabel_eq_tensorLabel]
  unfold rawKetZero
  rw [← basisKetVec_zero_one]
  rw [raw_tensor_ket, castWidthVec_ket, raw_tensor_ket,
    castWidthVec_ket]

/-- The actual initial X layer followed by its actual low Walsh-Hadamard
layer prepares the zeroth aligned residual block. -/
private theorem initialPreparation_applyVec_zero_eq_residualBlock_zero
    (b : BinaryExpansion N) :
    (UnitaryCircuit.seq b.initialXLayer b.lowHadamardLayer).applyVec
        (NormalizedVector.ket (R := Qubits b.width) 0 :
          HilbertVector (Qubits b.width)) =
      b.residualBlock 0 := by
  let high := (basisKetVec (b.residualHighLabel 0))
  let lowZero := rawKetZero b.first
  let lowUniform := (WalshHadamard.uniformState b.first :
    HilbertVector (Qubits b.first))
  have hfirst : b.first < b.width := b.first_lt_width
  have htop : (b.width - b.first - 1) + 1 = b.width - b.first := by
    omega
  have houter : (b.width - b.first) + b.first = b.width := by
    have hle : b.first ≤ b.last :=
      b.ell_strict.monotone (Fin.zero_le _)
    unfold width
    omega
  have hleft : ((b.width - b.first - 1) + 1) + b.first = b.width := by
    omega
  have hassoc : ((b.width - b.first - 1) + 1) + b.first =
      (b.width - b.first - 1) + (1 + b.first) := by
    omega
  have hresidual : (b.width - b.first - 1) + (1 + b.first) = b.width := by
    omega
  calc
    (UnitaryCircuit.seq b.initialXLayer b.lowHadamardLayer).applyVec
        (NormalizedVector.ket (R := Qubits b.width) 0 :
          HilbertVector (Qubits b.width)) =
      b.lowHadamardLayer.applyVec
        (b.initialXLayer.applyVec
          (NormalizedVector.ket (R := Qubits b.width) 0 :
            HilbertVector (Qubits b.width))) := by
          rw [UnitaryCircuit.applyVec_seq]
    _ = b.lowHadamardLayer.applyVec
        (NormalizedVector.ket (R := Qubits b.width) b.initialXLabel :
          HilbertVector (Qubits b.width)) := by
          rw [b.initialXLayer_applyVec_zero]
    _ = b.lowHadamardLayer.applyVec
        (castWidthVec houter
          (HilbertVector.tensor
            (castWidthVec htop
              (HilbertVector.tensor high (ket0 : HilbertVector (Qubits 1))))
            lowZero)) := by
          convert congrArg b.lowHadamardLayer.applyVec
            b.initialXLabel_raw_tensor using 1
    _ = castWidthVec houter
          (HilbertVector.tensor
            (castWidthVec htop
              (HilbertVector.tensor high (ket0 : HilbertVector (Qubits 1))))
            lowUniform) := by
          simpa [high, lowZero, lowUniform, rawKetZero, basisKetVec] using
            b.lowHadamardLayer_applyVec_tensor
              (castWidthVec htop
                (HilbertVector.tensor high (ket0 : HilbertVector (Qubits 1))))
    _ = castWidthVec hleft
          (HilbertVector.tensor
            (HilbertVector.tensor high (ket0 : HilbertVector (Qubits 1)))
            lowUniform) := by
          simpa using
            (castWidthVec_tensor_left_transport htop houter
              (HilbertVector.tensor high (ket0 : HilbertVector (Qubits 1)))
              lowUniform)
    _ = castWidthVec hresidual
          (HilbertVector.tensor high
            (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) lowUniform)) := by
          calc
            castWidthVec hleft
                (HilbertVector.tensor
                  (HilbertVector.tensor high (ket0 : HilbertVector (Qubits 1)))
                  lowUniform) =
                castWidthVec hresidual
                  (castWidthVec hassoc
                    (HilbertVector.tensor
                      (HilbertVector.tensor high (ket0 : HilbertVector (Qubits 1)))
                      lowUniform)) := by
                    rw [castWidthVec_trans]
            _ = _ := by
                    rw [raw_tensor_assoc]
    _ = b.residualBlock 0 := by
          simpa [high, lowUniform, first] using
            (b.residualBlock_tensor_factor (0 : Fin (b.s + 1))).symm

/-- The source position represented by a natural prefix length.  Clamping is
only a total-definition device; every use in the gap induction carries the
corresponding `count ≤ s` bound and therefore has its literal value. -/
private def sourcePosition (b : BinaryExpansion N) (count : Nat) :
    Fin (b.s + 1) :=
  ⟨min count b.s, by omega⟩

private theorem sourcePosition_eq_of_le (b : BinaryExpansion N)
    {count : Nat} (hcount : count ≤ b.s) :
    b.sourcePosition count = ⟨count, by omega⟩ := by
  apply Fin.ext
  simp [sourcePosition, Nat.min_eq_left hcount]

private theorem sourcePosition_lt_of_lt (b : BinaryExpansion N)
    {left right : Nat} (hright : right ≤ b.s) (hleft : left < right) :
    (b.sourcePosition left).val < (b.sourcePosition right).val := by
  simp [sourcePosition, Nat.min_eq_left (Nat.le_trans (Nat.le_of_lt hleft) hright),
    Nat.min_eq_left hright, hleft]

/-- The accepted portion after `count` source gaps, kept as the actual
finite raw-vector sum on its already finalized residual blocks. -/
private def acceptedPrefix (b : BinaryExpansion N) (count : Nat) :
    HilbertVector (Qubits b.width) :=
  ∑ index ∈ Finset.range count,
    (b.blockWeight (b.sourcePosition index) : ℂ) •
      b.residualBlock (b.sourcePosition index)

/-- The exact residual-block invariant after a natural number of literal
source-gap stages. -/
private def prefixState (b : BinaryExpansion N) (count : Nat) :
    HilbertVector (Qubits b.width) :=
  b.acceptedPrefix count +
    (b.residualWeight (b.sourcePosition count) : ℂ) •
      b.residualBlock (b.sourcePosition count)

private theorem acceptedPrefix_succ (b : BinaryExpansion N) (count : Nat) :
    b.acceptedPrefix (count + 1) = b.acceptedPrefix count +
      (b.blockWeight (b.sourcePosition count) : ℂ) •
        b.residualBlock (b.sourcePosition count) := by
  unfold acceptedPrefix
  rw [Finset.sum_range_succ]

/-- The next literal stage fixes the finite sum of all previously accepted
blocks.  This is a direct linear lift of `gapStage_applyVec_residualBlock_eq_self`. -/
private theorem gapStage_applyVec_acceptedPrefix
    (b : BinaryExpansion N) (count : Nat) (hcount : count < b.s) :
    (b.gapStage ⟨count, hcount⟩).applyVec (b.acceptedPrefix count) =
      b.acceptedPrefix count := by
  unfold acceptedPrefix
  rw [circuit_applyVec_finset_sum]
  apply Finset.sum_congr rfl
  intro index hindex
  rw [UnitaryCircuit.applyVec_smul]
  congr 1
  apply b.gapStage_applyVec_residualBlock_eq_self ⟨count, hcount⟩
  have hposition := b.sourcePosition_lt_of_lt (Nat.le_of_lt hcount)
    (Finset.mem_range.mp hindex)
  rw [b.sourcePosition_eq_of_le (Nat.le_of_lt hcount)] at hposition
  simpa using hposition

/-- One actual gap stage advances the raw finite residual invariant.  The
only scalar rewrites are the two source-angle identities proved above. -/
private theorem gapStage_applyVec_prefixState
    (b : BinaryExpansion N) (count : Nat) (hcount : count < b.s) :
    (b.gapStage ⟨count, hcount⟩).applyVec (b.prefixState count) =
      b.prefixState (count + 1) := by
  let gap : Fin b.s := ⟨count, hcount⟩
  have hcurrent : b.sourcePosition count = gap.castSucc := by
    apply Fin.ext
    simp [sourcePosition, gap, Nat.min_eq_left (Nat.le_of_lt hcount)]
  have hnext : b.sourcePosition (count + 1) = gap.succ := by
    apply Fin.ext
    simp [sourcePosition, gap, Nat.min_eq_left (by omega : count + 1 ≤ b.s)]
  have hretain :
      (b.residualWeight gap.castSucc : ℂ) *
          (Real.cos (b.sourceAngle gap / 2) : ℂ) =
        (b.blockWeight gap.castSucc : ℂ) := by
    exact_mod_cast b.residualWeight_mul_cos_half_sourceAngle gap
  have hopen :
      (b.residualWeight gap.castSucc : ℂ) *
          (-(Real.sin (b.sourceAngle gap / 2)) : ℂ) =
        (b.residualWeight gap.succ : ℂ) := by
    exact_mod_cast b.residualWeight_mul_neg_sin_half_sourceAngle gap
  unfold prefixState
  rw [UnitaryCircuit.applyVec_add,
    b.gapStage_applyVec_acceptedPrefix count hcount,
    UnitaryCircuit.applyVec_smul, hcurrent,
    b.gapStage_applyVec_residualBlock_active gap]
  simp only [smul_add, smul_smul]
  rw [hopen, hretain, ← hnext, ← hcurrent,
    b.acceptedPrefix_succ count]
  abel

/-- The increasing finite prefix of literal gap stages realizes exactly the
natural-index residual invariant.  The `List.ofFn` induction mirrors the
actual `indexedProductNamed` fold order, rather than merely counting stages. -/
private theorem gapPrefix_foldl_applyVec (b : BinaryExpansion N) :
    ∀ (count : Nat) (hcount : count ≤ b.s),
      (List.ofFn (fun index : Fin count =>
        b.gapStage (Fin.castLE hcount index))).foldl
          (fun state circuit => circuit.applyVec state)
          (b.residualBlock 0) =
        b.prefixState count := by
  intro count
  induction count with
  | zero =>
      intro _
      simp [prefixState, acceptedPrefix, sourcePosition,
        b.residualWeight_zero]
  | succ count induction =>
      intro hcount
      have hprev : count ≤ b.s := Nat.le_of_succ_le hcount
      have hstep : count < b.s := by
        omega
      have hprefix :
          (List.ofFn (fun index : Fin count =>
            b.gapStage (Fin.castLE hcount index.castSucc))).foldl
              (fun state circuit => circuit.applyVec state)
              (b.residualBlock 0) = b.prefixState count := by
          have hcast : ∀ index : Fin count,
              Fin.castLE hcount index.castSucc = Fin.castLE hprev index := by
            intro index
            apply Fin.ext
            rfl
          simpa only [hcast] using induction hprev
      have hlast : Fin.castLE hcount (Fin.last count) =
          (⟨count, hstep⟩ : Fin b.s) := by
        apply Fin.ext
        rfl
      rw [List.ofFn_succ', List.concat_eq_append, List.foldl_concat,
        hprefix, hlast]
      exact b.gapStage_applyVec_prefixState count hstep

/-- At the last natural prefix, the accepted finite range and the remaining
last residual are exactly the full finite family of source blocks. -/
private theorem prefixState_last_eq_blockSum (b : BinaryExpansion N) :
    b.prefixState b.s =
      ∑ index : Fin (b.s + 1),
        (b.blockWeight index : ℂ) • b.residualBlock index := by
  have hlast : b.sourcePosition b.s = Fin.last b.s := by
    apply Fin.ext
    simp [sourcePosition]
  have hspos := b.s_pos
  let penultimate : Fin b.s := ⟨b.s - 1, by omega⟩
  have hsucc : penultimate.succ = Fin.last b.s := by
    apply Fin.ext
    change (b.s - 1) + 1 = b.s
    omega
  have htail : b.tailMass penultimate.castSucc =
      2 ^ b.ell penultimate.succ := by
    have hstep := b.tailMass_eq_pow_add_tailMass_succ penultimate
    have hlastTail : b.tailMass penultimate.succ = 0 := by
      rw [hsucc, b.tailMass_last]
    rw [hlastTail, Nat.add_zero] at hstep
    exact hstep
  have hremaining : N - b.lowerMass (Fin.last b.s) =
      2 ^ b.ell (Fin.last b.s) := by
    calc
      N - b.lowerMass (Fin.last b.s) =
          N - b.lowerMass penultimate.succ := by rw [hsucc]
      _ = b.tailMass penultimate.castSucc :=
        b.N_sub_lowerMass_succ_eq_tailMass penultimate
      _ = 2 ^ b.ell penultimate.succ := htail
      _ = 2 ^ b.ell (Fin.last b.s) := by rw [hsucc]
  have hweight : b.residualWeight (Fin.last b.s) =
      b.blockWeight (Fin.last b.s) := by
    unfold residualWeight blockWeight
    rw [hremaining]
  have hsourcePosition (index : Fin b.s) :
      b.sourcePosition index.val = index.castSucc := by
    rw [b.sourcePosition_eq_of_le (Nat.le_of_lt index.isLt)]
    apply Fin.ext
    rfl
  have hfin :
      (∑ index : Fin b.s,
        (b.blockWeight index.castSucc : ℂ) • b.residualBlock index.castSucc) =
      ∑ index : Fin b.s,
        (b.blockWeight (b.sourcePosition index.val) : ℂ) •
          b.residualBlock (b.sourcePosition index.val) := by
    apply Finset.sum_congr rfl
    intro index _
    rw [hsourcePosition index]
  unfold prefixState acceptedPrefix
  rw [hlast, hweight, Fin.sum_univ_castSucc]
  congr 1
  rw [hfin]
  exact (Fin.sum_univ_eq_sum_range (fun index =>
    (b.blockWeight (b.sourcePosition index) : ℂ) •
      b.residualBlock (b.sourcePosition index)) b.s).symm

/-- The raw action of the complete literal pre-footprint Algorithm-1 tree is
the weighted sum of every aligned residual block. -/
private theorem algorithm1RawCircuit_applyVec_zero_blockSum
    (b : BinaryExpansion N) :
    b.algorithm1RawCircuit.applyVec
        (NormalizedVector.ket (R := Qubits b.width) 0) =
      ∑ index : Fin (b.s + 1),
        (b.blockWeight index : ℂ) • b.residualBlock index := by
  unfold algorithm1RawCircuit
  rw [UnitaryCircuit.applyVec_indexedProductNamed,
    b.initialPreparation_applyVec_zero_eq_residualBlock_zero]
  have hfold := b.gapPrefix_foldl_applyVec b.s (Nat.le_refl _)
  rw [b.prefixState_last_eq_blockSum] at hfold
  simpa [idleCircuit, UnitaryCircuit.applyVec_identity] using hfold

/-- The aligned source intervals cover every address below the certified
binary sum.  The proof chooses the first descending tail base not exceeding
the address; adjacent-tail arithmetic makes that chosen interval active. -/
private theorem residualSupport_exists_of_lt_N (b : BinaryExpansion N)
    {address : Nat} (haddress : address < N) :
    ∃ source : Fin (b.s + 1), b.residualSupport source address := by
  classical
  let predicate : Nat → Prop := fun count =>
    count ≤ b.s ∧ b.tailMass (b.sourcePosition count) ≤ address
  have hexists : ∃ count, predicate count := by
    refine ⟨b.s, Nat.le_refl _, ?_⟩
    have hlast : b.sourcePosition b.s = Fin.last b.s := by
      apply Fin.ext
      simp [sourcePosition]
    rw [hlast, b.tailMass_last]
    omega
  let count := Nat.find hexists
  have hspec : predicate count := by
    simpa [count] using Nat.find_spec hexists
  have hspec' : count ≤ b.s ∧
      b.tailMass (b.sourcePosition count) ≤ address := by
    simpa [predicate] using hspec
  refine ⟨b.sourcePosition count, hspec'.2, ?_⟩
  by_cases hzero : count = 0
  · rw [hzero]
    have hposition : b.sourcePosition 0 = (0 : Fin (b.s + 1)) :=
      b.sourcePosition_eq_of_le (by omega)
    rw [hposition]
    have hpartition :=
      b.prefixMass_add_current_add_tailMass (⟨0, b.s_pos⟩ : Fin b.s)
    rw [b.prefixMass_zero] at hpartition
    have htop : b.tailMass (0 : Fin (b.s + 1)) +
        2 ^ b.ell (0 : Fin (b.s + 1)) = N := by
      simpa [Nat.add_comm] using hpartition
    omega
  · have hcountPos : 0 < count := Nat.pos_of_ne_zero hzero
    have hprevLe : count - 1 ≤ b.s := by
      omega
    have hnotPrev : ¬ predicate (count - 1) := by
      intro hprev
      have hleast : count ≤ count - 1 := by
        dsimp [count]
        exact Nat.find_min' hexists hprev
      omega
    have hprevBase : address < b.tailMass (b.sourcePosition (count - 1)) := by
      have hnot : ¬ b.tailMass (b.sourcePosition (count - 1)) ≤ address := by
        intro hle
        exact hnotPrev ⟨hprevLe, hle⟩
      omega
    let gap : Fin b.s := ⟨count - 1, by omega⟩
    have hprevPosition : b.sourcePosition (count - 1) = gap.castSucc := by
      apply Fin.ext
      simp [sourcePosition, gap,
        Nat.min_eq_left (by omega : count - 1 ≤ b.s)]
    have hcurrentPosition : b.sourcePosition count = gap.succ := by
      apply Fin.ext
      change min count b.s = count - 1 + 1
      rw [Nat.min_eq_left hspec'.1]
      omega
    have htail := b.tailMass_eq_pow_add_tailMass_succ gap
    rw [hcurrentPosition]
    rw [hprevPosition] at hprevBase
    omega

/-- A certified address lies in at most one aligned source interval. -/
private theorem residualSupport_unique (b : BinaryExpansion N)
    {left right : Fin (b.s + 1)} {address : Nat}
    (hleft : b.residualSupport left address)
    (hright : b.residualSupport right address) : left = right := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact b.residualSupport_disjoint_of_lt hlt address ⟨hleft, hright⟩
  · exact b.residualSupport_disjoint_of_lt hgt address ⟨hright, hleft⟩

/-- Multiplying a normalized source block by its Algorithm-1 accepted weight
gives exactly the common target amplitude. -/
private theorem blockWeight_mul_residualAmplitude
    (b : BinaryExpansion N) (source : Fin (b.s + 1)) :
    (b.blockWeight source : ℂ) *
        WalshHadamard.invSqrtCard (b.ell source) = invSqrtCard N := by
  have hpow : 0 < ((2 ^ b.ell source : Nat) : ℝ) := by
    positivity
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast b.N_pos
  have hpowSqrt : (Real.sqrt ((2 ^ b.ell source : Nat) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hpow)
  have hNSqrt : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hNreal)
  unfold blockWeight WalshHadamard.invSqrtCard invSqrtCard
  rw [Real.sqrt_div (Nat.cast_nonneg _), Complex.ofReal_div]
  field_simp [hpowSqrt, hNSqrt]

/-- The finite weighted residual decomposition is pointwise the desired
uniform vector on `0, …, N - 1`.  Coverage comes from the adjacent source
intervals and uniqueness from their proved disjointness. -/
private theorem blockSum_eq_uniformState_raw (b : BinaryExpansion N) :
    (∑ source : Fin (b.s + 1),
      (b.blockWeight source : ℂ) • b.residualBlock source) =
      (uniformState N b.width b.N_pos b.fits_proof :
        HilbertVector (Qubits b.width)) := by
  apply WithLp.ofLp_injective
  funext address
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [uniformState_apply b.N_pos b.fits_proof address]
  by_cases haddress : address.val < N
  · obtain ⟨source, hsupport⟩ := b.residualSupport_exists_of_lt_N haddress
    rw [Finset.sum_eq_single source]
    · have hsupport' :
          b.tailMass source ≤ address.val ∧
            address.val < b.tailMass source + 2 ^ b.ell source := by
        simpa only [residualSupport] using hsupport
      rw [residualBlock_apply, if_pos hsupport',
        b.blockWeight_mul_residualAmplitude source]
      simp [haddress]
    · intro other _ hne
      have hnot : ¬ b.residualSupport other address.val := by
        intro hother
        have heq := b.residualSupport_unique hother hsupport
        exact hne heq
      rw [b.residualBlock_apply_of_not_support other address hnot]
      simp
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [haddress]
    · intro source _
      have hnot : ¬ b.residualSupport source address.val := by
        intro hsupport
        have hbound := b.tailMass_add_current_le source
        exact haddress (lt_of_lt_of_le hsupport.2 hbound)
      rw [b.residualBlock_apply_of_not_support source address hnot]
      simp

end BinaryExpansion

namespace BinaryExpansion

variable {N : Nat}

/-- The literal intrinsic Algorithm-1 circuit prepares the exact range-uniform
state from the all-zero input.  This is obtained by evaluating the same
concrete schedule whose footprint and elementary ledger are exposed below. -/
theorem algorithm1Circuit_apply_zero (b : BinaryExpansion N) :
    b.algorithm1Circuit.applyNormalized
        (NormalizedVector.ket (R := Qubits b.width) 0) =
      uniformState N b.width b.N_pos b.fits_proof := by
  rw [algorithm1Circuit, withCanonicalFootprint_applyNormalized]
  apply NormalizedVector.ext
  intro index
  have hraw := congrArg
    (fun state : HilbertVector (Qubits b.width) => state index)
    ((b.algorithm1RawCircuit_applyVec_zero_blockSum).trans
      b.blockSum_eq_uniformState_raw)
  simpa only [UnitaryCircuit.applyNormalized_coe] using hraw

/-- The same literal preparation acts on a wider endpoint register by a
high all-zero identity tensor, preserving its exact range-uniform output. -/
theorem algorithm1CircuitPadded_apply_zero (b : BinaryExpansion N)
    {t : Nat} (hwidth : b.width ≤ t) :
    (b.algorithm1CircuitPadded hwidth).applyNormalized
        (NormalizedVector.ket (R := Qubits t) 0) =
      uniformState N t b.N_pos (fits_pad b.fits_proof hwidth) := by
  unfold algorithm1CircuitPadded
  rw [withCanonicalFootprint_applyNormalized]
  exact padHigh_apply_zero b.N_pos b.fits_proof hwidth
    b.algorithm1Circuit b.algorithm1Circuit_apply_zero

end BinaryExpansion

@[simp]
theorem rotY_unit_depth (θ : ℝ) :
    (rotY θ).evaluatedEventDepth (fun _ => 1) = 1 :=
  rfl

@[simp]
theorem X_unit_depth : X.evaluatedEventDepth (fun _ => 1) = 1 :=
  rfl

@[simp]
theorem X_eventTrace :
    X.eventTrace = [Gate.atomicEvent (.builtin "x")] :=
  rfl

@[simp]
private theorem X_eventCost_local :
    X.eventCost = ResourcePool.singleton xEvent :=
  rfl

@[simp]
theorem CNOT_unit_depth : CNOT.evaluatedEventDepth (fun _ => 1) = 1 :=
  rfl

@[simp]
theorem identity_unit_depth (R : Register) (physical_idx : List Nat)
    (physical_idx_nodup : physical_idx.Nodup) :
    (UnitaryCircuit.identity R physical_idx physical_idx_nodup).evaluatedEventDepth
        (fun _ => 1) = 0 :=
  rfl

@[simp]
theorem shiftPhysicalIdx_unit_depth {R : Register} (offset : Nat)
    (circuit : UnitaryCircuit R) :
    (UnitaryCircuit.shiftPhysicalIdx offset circuit).evaluatedEventDepth (fun _ => 1) =
      circuit.evaluatedEventDepth (fun _ => 1) := by
  simp [UnitaryCircuit.evaluatedEventDepth]

@[simp]
theorem targetRotY_eventTrace (θ : ℝ) :
    (targetRotY θ).eventTrace = [(rotYLeaf θ).event] := by
  simp [targetRotY]

@[simp]
theorem controlX_eventTrace :
    controlX.eventTrace = [Gate.atomicEvent (.builtin "x")] := by
  simp [controlX]

@[simp]
theorem controlXParallelTargetRotY_eventTrace (θ : ℝ) :
    (controlXParallelTargetRotY θ).eventTrace =
      [Gate.atomicEvent (.builtin "x"), (rotYLeaf θ).event] := by
  simp [controlXParallelTargetRotY]

@[simp]
theorem controlledRotY_eventTrace (θ : ℝ) :
    (controlledRotY θ).eventTrace =
      [(rotYLeaf (θ / 2)).event, Gate.atomicEvent (.builtin "cnot"),
        (rotYLeaf (-(θ / 2))).event, Gate.atomicEvent (.builtin "cnot")] := by
  simp [controlledRotY]

@[simp]
theorem openControlledRotY_eventTrace (θ : ℝ) :
    (openControlledRotY θ).eventTrace =
      [Gate.atomicEvent (.builtin "x"), (rotYLeaf (θ / 2)).event,
        Gate.atomicEvent (.builtin "cnot"), (rotYLeaf (-(θ / 2))).event,
        Gate.atomicEvent (.builtin "cnot"), Gate.atomicEvent (.builtin "x")] := by
  simp [openControlledRotY]

@[simp]
theorem controlledH_eventTrace :
    controlledH.eventTrace =
      [(rotYLeaf (Real.pi / 4)).event, Gate.atomicEvent (.builtin "cnot"),
        (rotYLeaf (-(Real.pi / 4))).event] := by
  simp [controlledH]

@[simp]
theorem openControlledH_eventTrace :
    openControlledH.eventTrace =
      [Gate.atomicEvent (.builtin "x"), (rotYLeaf (Real.pi / 4)).event,
        Gate.atomicEvent (.builtin "cnot"), Gate.atomicEvent (.builtin "x"),
        (rotYLeaf (-(Real.pi / 4))).event] := by
  simp [openControlledH]

/-- Exact one-qubit and CNOT occurrences of the two literal open-control
lowerings.  These counts are derived from their concrete event traces. -/
theorem openControlledRotY_singleQubitCount (θ : ℝ) :
    (openControlledRotY θ).eventTrace.countP singleQubitEvent = 4 := by
  rw [openControlledRotY_eventTrace]
  simp [singleQubitEvent, Resource.GateLabel.builtin,
    Resource.GateLabel.declared]

theorem openControlledRotY_cnotCount (θ : ℝ) :
    (openControlledRotY θ).eventTrace.count cnotEvent = 2 := by
  rw [openControlledRotY_eventTrace]
  simp [cnotEvent, Resource.GateLabel.builtin,
    Resource.GateLabel.declared]

theorem openControlledH_singleQubitCount :
    openControlledH.eventTrace.countP singleQubitEvent = 4 := by
  rw [openControlledH_eventTrace]
  simp [singleQubitEvent, Resource.GateLabel.builtin,
    Resource.GateLabel.declared]

theorem openControlledH_cnotCount :
    openControlledH.eventTrace.count cnotEvent = 1 := by
  rw [openControlledH_eventTrace]
  simp [cnotEvent, Resource.GateLabel.builtin,
    Resource.GateLabel.declared]

theorem openControlledRotYRightControl_singleQubitCount (θ : ℝ) :
    (openControlledRotYRightControl θ).eventTrace.countP singleQubitEvent = 4 := by
  rw [openControlledRotYRightControl_eventTrace]
  simp [singleQubitEvent, Resource.GateLabel.builtin,
    Resource.GateLabel.declared]

theorem openControlledRotYRightControl_cnotCount (θ : ℝ) :
    (openControlledRotYRightControl θ).eventTrace.count cnotEvent = 2 := by
  rw [openControlledRotYRightControl_eventTrace]
  simp [cnotEvent, Resource.GateLabel.builtin,
    Resource.GateLabel.declared]

@[simp]
theorem controlledRotY_unit_depth (θ : ℝ) :
    (controlledRotY θ).evaluatedEventDepth (fun _ => 1) = 4 := by
  simp [controlledRotY, targetRotY]

@[simp]
theorem openControlledRotY_unit_depth (θ : ℝ) :
    (openControlledRotY θ).evaluatedEventDepth (fun _ => 1) = 5 := by
  simp [openControlledRotY, controlXParallelTargetRotY, targetRotY, controlX]

@[simp]
theorem controlledH_unit_depth :
    controlledH.evaluatedEventDepth (fun _ => 1) = 3 := by
  simp [controlledH, targetRotY]

@[simp]
theorem openControlledH_unit_depth :
    openControlledH.evaluatedEventDepth (fun _ => 1) = 3 := by
  simp [openControlledH, controlXParallelTargetRotY]

@[simp]
theorem rightControlledCNOT_unit_depth :
    rightControlledCNOT.evaluatedEventDepth (fun _ => 1) = 1 := by
  rfl

@[simp]
theorem openControlledRotYRightControl_unit_depth (θ : ℝ) :
    (openControlledRotYRightControl θ).evaluatedEventDepth (fun _ => 1) = 5 := by
  simp [openControlledRotYRightControl, targetRotYParallelRightControlX,
    targetFirstRotY, rightControlX]

/-! ### Literal resource projections -/

attribute [local simp] ResourcePool.count_singleton_of_ne
attribute [local simp] Multiset.count_replicate Multiset.mem_replicate
attribute [local simp] Resource.GateLabel.mk.injEq

@[simp]
theorem singleQubitCost_seq {width : Nat} (left right : UnitaryCircuit (Qubits width)) :
    singleQubitCost (UnitaryCircuit.seq left right) =
      singleQubitCost left + singleQubitCost right := by
  simp [singleQubitCost, ResourcePool.count_add]
  omega

@[simp]
theorem cnotCost_seq {width : Nat} (left right : UnitaryCircuit (Qubits width)) :
    cnotCost (UnitaryCircuit.seq left right) = cnotCost left + cnotCost right := by
  simp [cnotCost, ResourcePool.count_add]

@[simp]
theorem singleQubitCost_castWidth {source target : Nat} (h : source = target)
    (program : UnitaryCircuit (Qubits source)) :
    singleQubitCost (castWidth h program) = singleQubitCost program := by
  simp [singleQubitCost]

@[simp]
theorem cnotCost_castWidth {source target : Nat} (h : source = target)
    (program : UnitaryCircuit (Qubits source)) :
    cnotCost (castWidth h program) = cnotCost program := by
  simp [cnotCost]

@[simp]
theorem singleQubitCost_atWire {width : Nat} (wire : Fin width)
    (program : UnitaryCircuit (Qubits 1)) :
    singleQubitCost (atWire wire program) = singleQubitCost program := by
  simp [singleQubitCost]

@[simp]
theorem cnotCost_atWire {width : Nat} (wire : Fin width)
    (program : UnitaryCircuit (Qubits 1)) :
    cnotCost (atWire wire program) = cnotCost program := by
  simp [cnotCost]

@[simp]
theorem singleQubitCost_atSeparatedWires {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (program : UnitaryCircuit (Qubits 2)) :
    singleQubitCost (atSeparatedWires left right hleft program) =
      singleQubitCost program := by
  simp [singleQubitCost]

@[simp]
theorem cnotCost_atSeparatedWires {width : Nat}
    (left right : Fin width) (hleft : left.val < right.val)
    (program : UnitaryCircuit (Qubits 2)) :
    cnotCost (atSeparatedWires left right hleft program) = cnotCost program := by
  simp [cnotCost]

@[simp]
theorem singleQubitCost_withCanonicalFootprint {width : Nat}
    (program : UnitaryCircuit (Qubits width)) :
    singleQubitCost (withCanonicalFootprint program) = singleQubitCost program := by
  simp [singleQubitCost]

@[simp]
theorem cnotCost_withCanonicalFootprint {width : Nat}
    (program : UnitaryCircuit (Qubits width)) :
    cnotCost (withCanonicalFootprint program) = cnotCost program := by
  simp [cnotCost]

@[simp]
theorem singleQubitCost_padHigh {source target : Nat} (hwidth : source ≤ target)
    (program : UnitaryCircuit (Qubits source)) :
    singleQubitCost (padHigh hwidth program) = singleQubitCost program := by
  simp [singleQubitCost]

@[simp]
theorem cnotCost_padHigh {source target : Nat} (hwidth : source ≤ target)
    (program : UnitaryCircuit (Qubits source)) :
    cnotCost (padHigh hwidth program) = cnotCost program := by
  simp [cnotCost]

@[simp]
theorem singleQubitCost_rotY (θ : ℝ) : singleQubitCost (rotY θ) = 1 := by
  simp [singleQubitCost, rotationYEvent, Resource.GateLabel.builtin,
    Resource.GateLabel.declared]

@[simp]
theorem cnotCost_rotY (θ : ℝ) : cnotCost (rotY θ) = 0 := by
  simp [cnotCost, Resource.GateLabel.builtin,
    Resource.GateLabel.declared]

@[simp]
theorem singleQubitCost_H : singleQubitCost H = 1 := by
  simp [singleQubitCost, rotationYEvent, Resource.GateLabel.builtin,
    Resource.GateLabel.declared, Gate.atomicEventCost, Gate.atomicEvent,
    ResourcePool.count, ResourcePool.singleton]

@[simp]
theorem cnotCost_H : cnotCost H = 0 := by
  simp [cnotCost, Resource.GateLabel.builtin, Gate.atomicEventCost, Gate.atomicEvent,
    ResourcePool.count, ResourcePool.singleton]

@[simp]
theorem singleQubitCost_xAtWire {width : Nat} (wire : Fin width) :
    singleQubitCost (xAtWire wire) = 1 := by
  simp [xAtWire, singleQubitCost, rotationYEvent,
    QubitPrimitive.circuit_eventCost, QubitPrimitive.event,
    QubitPrimitive.gateLabel, Resource.GateLabel.builtin,
    Resource.GateLabel.declared, ResourcePool.count, ResourcePool.singleton]

@[simp]
theorem cnotCost_xAtWire {width : Nat} (wire : Fin width) :
    cnotCost (xAtWire wire) = 0 := by
  simp [xAtWire, cnotCost,
    QubitPrimitive.circuit_eventCost, QubitPrimitive.event,
    QubitPrimitive.gateLabel, Resource.GateLabel.builtin,
    ResourcePool.count, ResourcePool.singleton]

@[simp]
theorem singleQubitCost_rotYAtWire {width : Nat} (wire : Fin width) (θ : ℝ) :
    singleQubitCost (rotYAtWire wire θ) = 1 := by
  simp [rotYAtWire]

@[simp]
theorem cnotCost_rotYAtWire {width : Nat} (wire : Fin width) (θ : ℝ) :
    cnotCost (rotYAtWire wire θ) = 0 := by
  simp [rotYAtWire]

@[simp]
theorem singleQubitCost_openControlledH : singleQubitCost openControlledH = 4 := by
  simp [singleQubitCost, openControlledH, controlXParallelTargetRotY,
    rotationYEvent, Gate.atomicEventCost,
    Gate.atomicEvent, Resource.GateLabel.builtin,
    Resource.GateLabel.declared, ResourcePool.count, ResourcePool.singleton]

@[simp]
theorem cnotCost_openControlledH : cnotCost openControlledH = 1 := by
  simp [cnotCost, openControlledH, controlXParallelTargetRotY,
    Gate.atomicEventCost,
    Gate.atomicEvent, Resource.GateLabel.builtin,
    Resource.GateLabel.declared, ResourcePool.count, ResourcePool.singleton]

@[simp]
theorem singleQubitCost_openControlledRotYRightControl (θ : ℝ) :
    singleQubitCost (openControlledRotYRightControl θ) = 4 := by
  simp [singleQubitCost, openControlledRotYRightControl,
    targetRotYParallelRightControlX, targetFirstRotY, rightControlX,
    rightControlledCNOT, rotationYEvent, QubitPrimitive.circuit_eventCost,
    QubitPrimitive.event, QubitPrimitive.gateLabel,
    Resource.GateLabel.builtin,
    Resource.GateLabel.declared, ResourcePool.count, ResourcePool.singleton]

@[simp]
theorem cnotCost_openControlledRotYRightControl (θ : ℝ) :
    cnotCost (openControlledRotYRightControl θ) = 2 := by
  simp [cnotCost, openControlledRotYRightControl,
    targetRotYParallelRightControlX, targetFirstRotY, rightControlX,
    rightControlledCNOT, QubitPrimitive.circuit_eventCost,
    QubitPrimitive.event, QubitPrimitive.gateLabel,
    Resource.GateLabel.builtin,
    Resource.GateLabel.declared, ResourcePool.count, ResourcePool.singleton]

private theorem resourcePool_count_finset_sum
    {kind : ProblemKind} {Index : Type} [Fintype Index]
    (focus : Resource.Event kind) (pool : Index → ResourcePool kind) :
    ResourcePool.count focus (∑ index, pool index) =
      ∑ index, ResourcePool.count focus (pool index) := by
  classical
  have aux : ∀ indices : Finset Index,
      ResourcePool.count focus (∑ index ∈ indices, pool index) =
        ∑ index ∈ indices, ResourcePool.count focus (pool index) := by
    intro indices
    induction indices using Finset.induction with
    | empty => simp
    | @insert index rest hindex ih =>
        simp [Finset.sum_insert, hindex, ResourcePool.count_add, ih]
  simpa using aux Finset.univ

private theorem resourcePool_count_indexedProductNamed {width count : Nat}
    (focus : Resource.Event .quantum) (label : String)
    (start : UnitaryCircuit (Qubits width))
    (step : Fin count → UnitaryCircuit (Qubits width)) :
    ResourcePool.count focus
        (UnitaryCircuit.indexedProductNamed label count start step).eventCost =
      ResourcePool.count focus start.eventCost +
        ∑ index, ResourcePool.count focus (step index).eventCost := by
  simp only [UnitaryCircuit.indexedProductNamed_eventCost, ResourcePool.count_add]
  rw [resourcePool_count_finset_sum]

private theorem singleQubitCost_indexedProductNamed {width count : Nat}
    (label : String) (start : UnitaryCircuit (Qubits width))
    (step : Fin count → UnitaryCircuit (Qubits width)) :
    singleQubitCost (UnitaryCircuit.indexedProductNamed label count start step) =
      singleQubitCost start + ∑ index, singleQubitCost (step index) := by
  unfold singleQubitCost
  rw [resourcePool_count_indexedProductNamed,
    resourcePool_count_indexedProductNamed,
    resourcePool_count_indexedProductNamed]
  simp only [Finset.sum_add_distrib]
  omega

private theorem cnotCost_indexedProductNamed {width count : Nat}
    (label : String) (start : UnitaryCircuit (Qubits width))
    (step : Fin count → UnitaryCircuit (Qubits width)) :
    cnotCost (UnitaryCircuit.indexedProductNamed label count start step) =
      cnotCost start + ∑ index, cnotCost (step index) := by
  unfold cnotCost
  rw [resourcePool_count_indexedProductNamed]

@[simp]
theorem xAtWire_unit_depth {width : Nat} (wire : Fin width) :
    (xAtWire wire).evaluatedEventDepth (fun _ => 1) = 1 := by
  rfl

@[simp]
theorem rotYAtWire_unit_depth {width : Nat} (wire : Fin width) (θ : ℝ) :
    (rotYAtWire wire θ).evaluatedEventDepth (fun _ => 1) = 1 := by
  simp [rotYAtWire]

@[simp]
theorem singleQubitCost_openControlledHAt {width : Nat}
    (control target : Fin width) (hct : control.val < target.val) :
    singleQubitCost (openControlledHAt control target hct) = 4 := by
  simp [openControlledHAt]

@[simp]
theorem cnotCost_openControlledHAt {width : Nat}
    (control target : Fin width) (hct : control.val < target.val) :
    cnotCost (openControlledHAt control target hct) = 1 := by
  simp [openControlledHAt]

@[simp]
theorem singleQubitCost_openControlledRotYAt {width : Nat}
    (target control : Fin width) (htc : target.val < control.val) (θ : ℝ) :
    singleQubitCost (openControlledRotYAt target control htc θ) = 4 := by
  simp [openControlledRotYAt]

@[simp]
theorem cnotCost_openControlledRotYAt {width : Nat}
    (target control : Fin width) (htc : target.val < control.val) (θ : ℝ) :
    cnotCost (openControlledRotYAt target control htc θ) = 2 := by
  simp [openControlledRotYAt]

theorem openControlledHAt_unit_depth {width : Nat}
    (control target : Fin width) (hct : control.val < target.val) :
    (openControlledHAt control target hct).evaluatedEventDepth (fun _ => 1) = 3 := by
  simp [openControlledHAt]

theorem openControlledRotYAt_unit_depth {width : Nat}
    (target control : Fin width) (htc : target.val < control.val) (θ : ℝ) :
    (openControlledRotYAt target control htc θ).evaluatedEventDepth
        (fun _ => 1) = 5 := by
  simp [openControlledRotYAt]

private theorem elementary_forall_append {eventsLeft eventsRight : List (Resource.Event .quantum)}
    (left : List.Forall elementaryEvent eventsLeft)
    (right : List.Forall elementaryEvent eventsRight) :
    List.Forall elementaryEvent (eventsLeft ++ eventsRight) := by
  rw [List.forall_iff_forall_mem] at left right ⊢
  intro event hevent
  rcases List.mem_append.mp hevent with hleft | hright
  · exact left event hleft
  · exact right event hright

private theorem elementary_trace_seq {width : Nat}
    (left right : UnitaryCircuit (Qubits width))
    (hleft : List.Forall elementaryEvent left.eventTrace)
    (hright : List.Forall elementaryEvent right.eventTrace) :
    List.Forall elementaryEvent (UnitaryCircuit.seq left right).eventTrace := by
  simpa using elementary_forall_append hleft hright

private theorem elementary_trace_indexedProductNamed {width count : Nat}
    (label : String) (start : UnitaryCircuit (Qubits width))
    (step : Fin count → UnitaryCircuit (Qubits width))
    (hstart : List.Forall elementaryEvent start.eventTrace)
    (hstep : ∀ index, List.Forall elementaryEvent (step index).eventTrace) :
    List.Forall elementaryEvent
      (UnitaryCircuit.indexedProductNamed label count start step).eventTrace := by
  rw [UnitaryCircuit.indexedProductNamed_eventTrace, List.forall_iff_forall_mem]
  intro event hevent
  rcases List.mem_append.mp hevent with hstartEvent | hstepsEvent
  · exact (List.forall_iff_forall_mem.mp hstart) event hstartEvent
  · rcases List.mem_flatten.mp hstepsEvent with ⟨trace, htrace, heventTrace⟩
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp htrace
    exact (List.forall_iff_forall_mem.mp (hstep index)) event heventTrace

private theorem rotY_elementary_trace (θ : ℝ) :
    List.Forall elementaryEvent (rotY θ).eventTrace := by
  simp [elementaryEvent]

private theorem xAtWire_elementary_trace {width : Nat} (wire : Fin width) :
    List.Forall elementaryEvent (xAtWire wire).eventTrace := by
  simp [xAtWire, QubitPrimitive.circuit_eventTrace, QubitPrimitive.event,
    QubitPrimitive.gateLabel, elementaryEvent]

private theorem rotYAtWire_elementary_trace {width : Nat} (wire : Fin width)
    (θ : ℝ) :
    List.Forall elementaryEvent (rotYAtWire wire θ).eventTrace := by
  simpa [rotYAtWire] using rotY_elementary_trace θ

private theorem openControlledH_elementary_trace :
    List.Forall elementaryEvent openControlledH.eventTrace := by
  rw [openControlledH_eventTrace]
  simp [elementaryEvent]

private theorem openControlledRotYRightControl_elementary_trace (θ : ℝ) :
    List.Forall elementaryEvent (openControlledRotYRightControl θ).eventTrace := by
  rw [openControlledRotYRightControl_eventTrace]
  simp [elementaryEvent]

private theorem hadamardLayer_elementary_trace (width : Nat) :
    List.Forall elementaryEvent (WalshHadamard.hadamardLayer width).eventTrace := by
  rw [WalshHadamard.hadamardLayer_eventTrace]
  induction width with
  | zero => simp [WalshHadamard.parallelHadamardEventTrace]
  | succ width ih =>
      rw [WalshHadamard.parallelHadamardEventTrace]
      exact elementary_forall_append ih (by simp [elementaryEvent])

namespace BinaryExpansion

variable {N : Nat}

@[simp]
private theorem idleCircuit_singleQubitCost (width : Nat) :
    singleQubitCost (idleCircuit width) = 0 := by
  simp [idleCircuit, singleQubitCost]

@[simp]
private theorem idleCircuit_cnotCost (width : Nat) :
    cnotCost (idleCircuit width) = 0 := by
  simp [idleCircuit, cnotCost]

@[simp]
private theorem idleCircuit_unit_depth (width : Nat) :
    (idleCircuit width).evaluatedEventDepth (fun _ => 1) = 0 := by
  simp [idleCircuit]

private theorem idleCircuit_elementary_trace (width : Nat) :
    List.Forall elementaryEvent (idleCircuit width).eventTrace := by
  simp [idleCircuit]

private theorem initialXLayer_elementary_trace (b : BinaryExpansion N) :
    List.Forall elementaryEvent b.initialXLayer.eventTrace := by
  unfold initialXLayer
  apply elementary_trace_indexedProductNamed
  · exact idleCircuit_elementary_trace b.width
  · intro index
    exact xAtWire_elementary_trace (b.wire index.succ)

private theorem lowHadamardLayer_elementary_trace (b : BinaryExpansion N) :
    List.Forall elementaryEvent b.lowHadamardLayer.eventTrace := by
  simpa [lowHadamardLayer] using hadamardLayer_elementary_trace b.first

private theorem gapHadamardLayer_elementary_trace (b : BinaryExpansion N)
    (gap : Fin b.s) :
    List.Forall elementaryEvent (b.gapHadamardLayer gap).eventTrace := by
  unfold gapHadamardLayer
  apply elementary_trace_indexedProductNamed
  · exact idleCircuit_elementary_trace b.width
  · intro offset
    simpa [openControlledHAt] using openControlledH_elementary_trace

private theorem gapStage_elementary_trace (b : BinaryExpansion N) (gap : Fin b.s) :
    List.Forall elementaryEvent (b.gapStage gap).eventTrace := by
  unfold gapStage
  split_ifs with hfirst
  · exact elementary_trace_seq _ _
      (rotYAtWire_elementary_trace _ _) (b.gapHadamardLayer_elementary_trace gap)
  · exact elementary_trace_seq _ _
      (by simpa [openControlledRotYAt] using
        openControlledRotYRightControl_elementary_trace (b.sourceAngle gap))
      (b.gapHadamardLayer_elementary_trace gap)

/-- Every event in the exposed intrinsic schedule is literally an H, X, CNOT,
or `R_Y` leaf. -/
theorem algorithm1Circuit_elementary_trace (b : BinaryExpansion N) :
    List.Forall elementaryEvent b.algorithm1Circuit.eventTrace := by
  have hraw : List.Forall elementaryEvent b.algorithm1RawCircuit.eventTrace := by
    unfold algorithm1RawCircuit
    apply elementary_trace_indexedProductNamed
    · exact elementary_trace_seq _ _ b.initialXLayer_elementary_trace
        b.lowHadamardLayer_elementary_trace
    · intro gap
      exact b.gapStage_elementary_trace gap
  simpa [algorithm1Circuit] using hraw

theorem algorithm1CircuitPadded_elementary_trace (b : BinaryExpansion N)
    {t : Nat} (hwidth : b.width ≤ t) :
    List.Forall elementaryEvent (b.algorithm1CircuitPadded hwidth).eventTrace := by
  simpa [algorithm1CircuitPadded] using b.algorithm1Circuit_elementary_trace

/-- Exact ledger count for the source's initial addressed-X prefix. -/
theorem initialXLayer_singleQubitCost (b : BinaryExpansion N) :
    singleQubitCost b.initialXLayer = b.s := by
  unfold initialXLayer
  rw [singleQubitCost_indexedProductNamed]
  simp

theorem initialXLayer_cnotCost (b : BinaryExpansion N) :
    cnotCost b.initialXLayer = 0 := by
  unfold initialXLayer
  rw [cnotCost_indexedProductNamed]
  simp

theorem initialXLayer_unit_depth (b : BinaryExpansion N) :
    b.initialXLayer.evaluatedEventDepth (fun _ => 1) = b.s := by
  unfold initialXLayer
  rw [UnitaryCircuit.evaluatedEventDepth_indexedProductNamed]
  simp

/-- The parallel low Hadamard layer contributes one H coordinate for each
source-low bit and no CNOT coordinate. -/
theorem lowHadamardLayer_singleQubitCost (b : BinaryExpansion N) :
    singleQubitCost b.lowHadamardLayer = b.first := by
  simp [lowHadamardLayer, singleQubitCost, rotationYEvent,
    Resource.GateLabel.builtin, Resource.GateLabel.declared,
    ResourcePool.count, ResourcePool.singleton]

theorem lowHadamardLayer_cnotCost (b : BinaryExpansion N) :
    cnotCost b.lowHadamardLayer = 0 := by
  simp [lowHadamardLayer, cnotCost,
    Resource.GateLabel.builtin,
    ResourcePool.count, ResourcePool.singleton]

theorem lowHadamardLayer_unit_depth_le (b : BinaryExpansion N) :
    b.lowHadamardLayer.evaluatedEventDepth (fun _ => 1) ≤ 1 := by
  simp [lowHadamardLayer, UnitaryCircuit.evaluatedEventDepth,
    WalshHadamard.hadamardLayer_eventDepth,
    WalshHadamard.parallelHadamardEventDepth_unit_depth]
  split <;> omega

/-- One gap-H layer has four single-qubit leaves and one CNOT for every
literal source gap target. -/
theorem gapHadamardLayer_singleQubitCost (b : BinaryExpansion N)
    (gap : Fin b.s) :
    singleQubitCost (b.gapHadamardLayer gap) = 4 * b.gapWidth gap := by
  unfold gapHadamardLayer
  rw [singleQubitCost_indexedProductNamed]
  simp [gapWidth, Nat.mul_comm]

theorem gapHadamardLayer_cnotCost (b : BinaryExpansion N)
    (gap : Fin b.s) :
    cnotCost (b.gapHadamardLayer gap) = b.gapWidth gap := by
  unfold gapHadamardLayer
  rw [cnotCost_indexedProductNamed]
  simp [gapWidth]

theorem gapHadamardLayer_unit_depth (b : BinaryExpansion N)
    (gap : Fin b.s) :
    (b.gapHadamardLayer gap).evaluatedEventDepth (fun _ => 1) =
      3 * b.gapWidth gap := by
  unfold gapHadamardLayer
  rw [UnitaryCircuit.evaluatedEventDepth_indexedProductNamed]
  simp [gapWidth, Nat.mul_comm]

/-- A whole Algorithm-1 gap stage includes either one bare rotation or the
right-control open rotation, followed by its literal H gap layer. -/
theorem gapStage_singleQubitCost_le (b : BinaryExpansion N) (gap : Fin b.s) :
    singleQubitCost (b.gapStage gap) ≤ 4 * b.gapWidth gap + 4 := by
  unfold gapStage
  split_ifs with hfirst
  · rw [singleQubitCost_seq, singleQubitCost_rotYAtWire,
      b.gapHadamardLayer_singleQubitCost]
    omega
  · rw [singleQubitCost_seq, singleQubitCost_openControlledRotYAt,
      b.gapHadamardLayer_singleQubitCost]
    omega

theorem gapStage_cnotCost_le (b : BinaryExpansion N) (gap : Fin b.s) :
    cnotCost (b.gapStage gap) ≤ b.gapWidth gap + 2 := by
  unfold gapStage
  split_ifs with hfirst
  · rw [cnotCost_seq, cnotCost_rotYAtWire,
      b.gapHadamardLayer_cnotCost]
    omega
  · rw [cnotCost_seq, cnotCost_openControlledRotYAt,
      b.gapHadamardLayer_cnotCost]
    omega

theorem gapStage_unit_depth_le (b : BinaryExpansion N) (gap : Fin b.s) :
    (b.gapStage gap).evaluatedEventDepth (fun _ => 1) ≤
      3 * b.gapWidth gap + 5 := by
  unfold gapStage
  split_ifs with hfirst
  · rw [UnitaryCircuit.evaluatedEventDepth_seq, rotYAtWire_unit_depth,
      b.gapHadamardLayer_unit_depth]
    omega
  · rw [UnitaryCircuit.evaluatedEventDepth_seq, openControlledRotYAt_unit_depth,
      b.gapHadamardLayer_unit_depth]
    omega

private theorem first_le_last (b : BinaryExpansion N) : b.first ≤ b.last := by
  unfold first last
  exact b.ell_strict.monotone (Fin.zero_le _)

private theorem algorithm1RawCircuit_singleQubitCost_le (b : BinaryExpansion N) :
    singleQubitCost b.algorithm1RawCircuit ≤
      b.s + b.first +
        ∑ gap : Fin b.s, (4 * b.gapWidth gap + 4) := by
  unfold algorithm1RawCircuit
  rw [singleQubitCost_indexedProductNamed, singleQubitCost_seq,
    b.initialXLayer_singleQubitCost, b.lowHadamardLayer_singleQubitCost]
  gcongr with gap
  exact b.gapStage_singleQubitCost_le gap

private theorem algorithm1RawCircuit_cnotCost_le (b : BinaryExpansion N) :
    cnotCost b.algorithm1RawCircuit ≤
      ∑ gap : Fin b.s, (b.gapWidth gap + 2) := by
  unfold algorithm1RawCircuit
  rw [cnotCost_indexedProductNamed, cnotCost_seq,
    b.initialXLayer_cnotCost, b.lowHadamardLayer_cnotCost]
  simp only [zero_add]
  apply Finset.sum_le_sum
  intro gap _
  exact b.gapStage_cnotCost_le gap

private theorem algorithm1RawCircuit_unit_depth_le (b : BinaryExpansion N) :
    b.algorithm1RawCircuit.evaluatedEventDepth (fun _ => 1) ≤
      b.s + 1 + ∑ gap : Fin b.s, (3 * b.gapWidth gap + 5) := by
  unfold algorithm1RawCircuit
  rw [UnitaryCircuit.evaluatedEventDepth_indexedProductNamed,
    UnitaryCircuit.evaluatedEventDepth_seq, b.initialXLayer_unit_depth]
  have hlow := b.lowHadamardLayer_unit_depth_le
  have hsteps :
      (∑ gap : Fin b.s,
        (b.gapStage gap).evaluatedEventDepth (fun _ => 1)) ≤
        ∑ gap : Fin b.s, (3 * b.gapWidth gap + 5) :=
    Finset.sum_le_sum fun gap _ => b.gapStage_unit_depth_le gap
  omega

/-- The one-preparation single-qubit budget is derived from the exact literal
event pool of `algorithm1Circuit`. -/
theorem algorithm1Circuit_single_qubit_bound (b : BinaryExpansion N) :
    singleQubitCost b.algorithm1Circuit ≤ b.singleQubitBound := by
  rw [algorithm1Circuit, singleQubitCost_withCanonicalFootprint]
  have hraw := b.algorithm1RawCircuit_singleQubitCost_le
  have hsum := b.sum_gapWidth
  have hfirst := b.first_le_last
  have hfour : (∑ _gap : Fin b.s, 4) = 4 * b.s := by
    simp [Nat.mul_comm]
  unfold singleQubitBound
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hraw
  rw [hfour, hsum] at hraw
  omega

/-- The literal CNOT budget is the source gap-width sum plus two CNOTs per
open controlled rotation. -/
theorem algorithm1Circuit_cnot_bound (b : BinaryExpansion N) :
    cnotCost b.algorithm1Circuit ≤ b.cnotBound := by
  rw [algorithm1Circuit, cnotCost_withCanonicalFootprint]
  have hraw := b.algorithm1RawCircuit_cnotCost_le
  have hsum := b.sum_gapWidth
  have htwo : (∑ _gap : Fin b.s, 2) = 2 * b.s := by
    simp [Nat.mul_comm]
  unfold cnotBound
  rw [Finset.sum_add_distrib] at hraw
  rw [htwo, hsum] at hraw
  omega

/-- The sequential unit-depth ledger of the same literal circuit meets the
one-preparation source depth envelope. -/
theorem algorithm1Circuit_depth_bound (b : BinaryExpansion N) :
    b.algorithm1Circuit.evaluatedEventDepth (fun _ => 1) ≤ b.depthBound := by
  rw [algorithm1Circuit, withCanonicalFootprint_evaluatedEventDepth]
  have hraw := b.algorithm1RawCircuit_unit_depth_le
  have hsum := b.sum_gapWidth
  have hstrict := b.s_le_gapWidth_sum
  rw [hsum] at hstrict
  have hfive : (∑ _gap : Fin b.s, 5) = 5 * b.s := by
    simp [Nat.mul_comm]
  unfold depthBound
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hraw
  rw [hfive, hsum] at hraw
  omega

/-- Padding is a true high-zero identity tensor, so its literal event-pool
projections and critical-path value remain those of the intrinsic circuit. -/
@[simp]
theorem algorithm1CircuitPadded_singleQubitCost (b : BinaryExpansion N)
    {t : Nat} (hwidth : b.width ≤ t) :
    singleQubitCost (b.algorithm1CircuitPadded hwidth) =
      singleQubitCost b.algorithm1Circuit := by
  simp [algorithm1CircuitPadded]

@[simp]
theorem algorithm1CircuitPadded_cnotCost (b : BinaryExpansion N)
    {t : Nat} (hwidth : b.width ≤ t) :
    cnotCost (b.algorithm1CircuitPadded hwidth) = cnotCost b.algorithm1Circuit := by
  simp [algorithm1CircuitPadded]

theorem algorithm1CircuitPadded_depth (b : BinaryExpansion N)
    {t : Nat} (hwidth : b.width ≤ t) :
    (b.algorithm1CircuitPadded hwidth).evaluatedEventDepth (fun _ => 1) =
      b.algorithm1Circuit.evaluatedEventDepth (fun _ => 1) := by
  simp [algorithm1CircuitPadded]

/-- High-zero padding preserves the intrinsic single-qubit envelope of the
same literal preparation circuit. -/
theorem algorithm1CircuitPadded_single_qubit_bound (b : BinaryExpansion N)
    {t : Nat} (hwidth : b.width ≤ t) :
    singleQubitCost (b.algorithm1CircuitPadded hwidth) ≤ b.singleQubitBound := by
  rw [b.algorithm1CircuitPadded_singleQubitCost hwidth]
  exact b.algorithm1Circuit_single_qubit_bound

/-- High-zero padding preserves the intrinsic CNOT envelope of the same
literal preparation circuit. -/
theorem algorithm1CircuitPadded_cnot_bound (b : BinaryExpansion N)
    {t : Nat} (hwidth : b.width ≤ t) :
    cnotCost (b.algorithm1CircuitPadded hwidth) ≤ b.cnotBound := by
  rw [b.algorithm1CircuitPadded_cnotCost hwidth]
  exact b.algorithm1Circuit_cnot_bound

/-- High-zero padding preserves the intrinsic unit-depth envelope of the
same literal preparation circuit. -/
theorem algorithm1CircuitPadded_depth_bound (b : BinaryExpansion N)
    {t : Nat} (hwidth : b.width ≤ t) :
    (b.algorithm1CircuitPadded hwidth).evaluatedEventDepth (fun _ => 1) ≤
      b.depthBound := by
  rw [b.algorithm1CircuitPadded_depth hwidth]
  exact b.algorithm1Circuit_depth_bound

/-- The complete literal Algorithm-1 event ledger is bounded by one common
single-qubit envelope for each permitted one-qubit coordinate and the source
CNOT envelope.  This is a coordinatewise fact about the *same* circuit used
for preparation, obtained from its elementary trace and aggregate counts. -/
theorem algorithm1Circuit_eventCost_le_elementaryEnvelope (b : BinaryExpansion N) :
    b.algorithm1Circuit.eventCost ≤
      ResourcePool.singleton (.gate (.builtin "hadamard")) b.singleQubitBound +
        (ResourcePool.singleton (.gate (.builtin "x")) b.singleQubitBound +
          (ResourcePool.singleton rotationYEvent b.singleQubitBound +
            ResourcePool.singleton cnotEvent b.cnotBound)) := by
  rw [ResourcePool.le_iff_count]
  intro event
  by_cases hhadamard : event = (.gate (.builtin "hadamard") : Resource.Event .quantum)
  · subst event
    have hsingle := b.algorithm1Circuit_single_qubit_bound
    calc
      ResourcePool.count (.gate (.builtin "hadamard")) b.algorithm1Circuit.eventCost ≤
          singleQubitCost b.algorithm1Circuit := by
            unfold singleQubitCost
            omega
      _ ≤ b.singleQubitBound := hsingle
      _ = ResourcePool.count (.gate (.builtin "hadamard"))
          (ResourcePool.singleton (.gate (.builtin "hadamard")) b.singleQubitBound +
            (ResourcePool.singleton (.gate (.builtin "x")) b.singleQubitBound +
              (ResourcePool.singleton rotationYEvent b.singleQubitBound +
                ResourcePool.singleton cnotEvent b.cnotBound))) := by
            simp [rotationYEvent, cnotEvent, Resource.GateLabel.builtin,
              Resource.GateLabel.declared, ResourcePool.count,
              ResourcePool.singleton]
  by_cases hx : event = (.gate (.builtin "x") : Resource.Event .quantum)
  · subst event
    have hsingle := b.algorithm1Circuit_single_qubit_bound
    calc
      ResourcePool.count (.gate (.builtin "x")) b.algorithm1Circuit.eventCost ≤
          singleQubitCost b.algorithm1Circuit := by
            unfold singleQubitCost
            omega
      _ ≤ b.singleQubitBound := hsingle
      _ = ResourcePool.count (.gate (.builtin "x"))
          (ResourcePool.singleton (.gate (.builtin "hadamard")) b.singleQubitBound +
            (ResourcePool.singleton (.gate (.builtin "x")) b.singleQubitBound +
              (ResourcePool.singleton rotationYEvent b.singleQubitBound +
                ResourcePool.singleton cnotEvent b.cnotBound))) := by
            simp [rotationYEvent, cnotEvent, Resource.GateLabel.builtin,
              Resource.GateLabel.declared, ResourcePool.count,
              ResourcePool.singleton]
  by_cases hrotation : event = rotationYEvent
  · subst event
    have hsingle := b.algorithm1Circuit_single_qubit_bound
    calc
      ResourcePool.count rotationYEvent b.algorithm1Circuit.eventCost ≤
          singleQubitCost b.algorithm1Circuit := by
            unfold singleQubitCost
            omega
      _ ≤ b.singleQubitBound := hsingle
      _ = ResourcePool.count rotationYEvent
          (ResourcePool.singleton (.gate (.builtin "hadamard")) b.singleQubitBound +
            (ResourcePool.singleton (.gate (.builtin "x")) b.singleQubitBound +
              (ResourcePool.singleton rotationYEvent b.singleQubitBound +
                ResourcePool.singleton cnotEvent b.cnotBound))) := by
            simp [rotationYEvent, cnotEvent, Resource.GateLabel.builtin,
              Resource.GateLabel.declared, ResourcePool.count,
              ResourcePool.singleton]
  by_cases hcnot : event = cnotEvent
  · subst event
    have hcnotBound := b.algorithm1Circuit_cnot_bound
    calc
      ResourcePool.count cnotEvent b.algorithm1Circuit.eventCost =
          cnotCost b.algorithm1Circuit := by rfl
      _ ≤ b.cnotBound := hcnotBound
      _ = ResourcePool.count cnotEvent
          (ResourcePool.singleton (.gate (.builtin "hadamard")) b.singleQubitBound +
            (ResourcePool.singleton (.gate (.builtin "x")) b.singleQubitBound +
              (ResourcePool.singleton rotationYEvent b.singleQubitBound +
                ResourcePool.singleton cnotEvent b.cnotBound))) := by
            simp [rotationYEvent, cnotEvent, Resource.GateLabel.builtin,
              Resource.GateLabel.declared, ResourcePool.count,
              ResourcePool.singleton]
  have hnotmem : event ∉ b.algorithm1Circuit.eventTrace := by
    intro hmem
    have hallowed : elementaryEvent event :=
      (List.forall_iff_forall_mem.mp b.algorithm1Circuit_elementary_trace) event hmem
    rcases hallowed with hallowed | hallowed | hallowed | hallowed
    · exact hhadamard (by simpa [hadamardEvent] using hallowed)
    · exact hx (by simpa [xEvent] using hallowed)
    · exact hrotation hallowed
    · exact hcnot hallowed
  have hzero : ResourcePool.count event b.algorithm1Circuit.eventCost = 0 := by
    rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
      ResourcePool.count_ofList,
      List.count_eq_zero_of_not_mem hnotmem]
  omega

end BinaryExpansion

/-- Resource projections of one physical elementary realization.  Correctness
is deliberately *not* a stored field: `algorithm1Circuit_apply_zero` must be proved
from the literal circuit tree and its gate semantics. -/
structure GateLevelCircuit {N : Nat} (b : BinaryExpansion N) where
  /-- The complete elementary circuit on the binary-expansion width. -/
  circuit : UnitaryCircuit (Qubits b.width)
  /-- Every occurrence is a concrete H, X, CNOT, or Y-rotation coordinate. -/
  elementary_trace : List.Forall elementaryEvent circuit.eventTrace
  /-- One-qubit coordinates in the literal event ledger meet the source
  envelope.  The ledger is derived from this same circuit's trace. -/
  single_qubit_bound :
    singleQubitCost circuit ≤ b.singleQubitBound
  /-- Literal CNOT coordinates in the same derived event ledger meet the
  source envelope. -/
  cnot_bound :
    cnotCost circuit ≤ b.cnotBound
  /-- The event-depth projection of the same circuit meets the source envelope. -/
  depth_bound :
    circuit.evaluatedEventDepth (fun _ => 1) ≤ b.depthBound

namespace BinaryExpansion

/-- The public resource view of the literal Algorithm-1 circuit.  Every
field below projects the same circuit tree; correctness remains the separate
state theorem proved from that tree's matrix action. -/
def algorithm1GateLevelCircuit {N : Nat} (b : BinaryExpansion N) :
    GateLevelCircuit b where
  circuit := b.algorithm1Circuit
  elementary_trace := b.algorithm1Circuit_elementary_trace
  single_qubit_bound := b.algorithm1Circuit_single_qubit_bound
  cnot_bound := b.algorithm1Circuit_cnot_bound
  depth_bound := b.algorithm1Circuit_depth_bound

end BinaryExpansion

end

end UniformSuperposition

end QuantumAlg

end
