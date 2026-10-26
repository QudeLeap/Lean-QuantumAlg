/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word39Chunk0 : List Letter := [.h, .s, .s, .h, .h, .s, .t, .h]
private def word39State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word39Step0 :
    word39Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word39State1 := by decide +kernel

private def word39Chunk1 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word39State2 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩⟩
private lemma word39Step1 :
    word39Chunk1.foldl (fun acc a => a.applyPacked acc)
      word39State1 = word39State2 := by decide +kernel

private def word39Chunk2 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word39State3 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word39Step2 :
    word39Chunk2.foldl (fun acc a => a.applyPacked acc)
      word39State2 = word39State3 := by decide +kernel

private def word39Chunk3 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word39State4 : PackedMat2 :=
    ⟨⟨⟨((9 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word39Step3 :
    word39Chunk3.foldl (fun acc a => a.applyPacked acc)
      word39State3 = word39State4 := by decide +kernel

private def word39Chunk4 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word39State5 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((-7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-7 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word39Step4 :
    word39Chunk4.foldl (fun acc a => a.applyPacked acc)
      word39State4 = word39State5 := by decide +kernel

private def word39Chunk5 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word39State6 : PackedMat2 :=
    ⟨⟨⟨((-9 : Dyadic) * half ^ 5),
        ((-11 : Dyadic) * half ^ 6)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((29 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 5),
        ((17 : Dyadic) * half ^ 6)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((-19 : Dyadic) * half ^ 6)⟩,
       ⟨((11 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 6)⟩,
       ⟨((-9 : Dyadic) * half ^ 5),
        ((19 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word39Step5 :
    word39Chunk5.foldl (fun acc a => a.applyPacked acc)
      word39State5 = word39State6 := by decide +kernel

private def word39Chunk6 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word39State7 : PackedMat2 :=
    ⟨⟨⟨((-7 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((-13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 6)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((-13 : Dyadic) * half ^ 6)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 1)⟩⟩⟩
private lemma word39Step6 :
    word39Chunk6.foldl (fun acc a => a.applyPacked acc)
      word39State6 = word39State7 := by decide +kernel

private def word39Chunk7 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word39State8 : PackedMat2 :=
    ⟨⟨⟨((-47 : Dyadic) * half ^ 7),
        ((43 : Dyadic) * half ^ 7)⟩,
       ⟨((-87 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 7),
        ((-13 : Dyadic) * half ^ 7)⟩,
       ⟨((-35 : Dyadic) * half ^ 7),
        ((3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 7),
        ((-23 : Dyadic) * half ^ 7)⟩,
       ⟨((-19 : Dyadic) * half ^ 7),
        ((3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-19 : Dyadic) * half ^ 7),
        ((67 : Dyadic) * half ^ 7)⟩,
       ⟨((-67 : Dyadic) * half ^ 7),
        ((-5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word39Step7 :
    word39Chunk7.foldl (fun acc a => a.applyPacked acc)
      word39State7 = word39State8 := by decide +kernel

private def word39Chunk8 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word39State9 : PackedMat2 :=
    ⟨⟨⟨((97 : Dyadic) * half ^ 7),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((43 : Dyadic) * half ^ 7)⟩,
       ⟨((-25 : Dyadic) * half ^ 7),
        ((-31 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((-43 : Dyadic) * half ^ 7)⟩,
       ⟨((-25 : Dyadic) * half ^ 7),
        ((-31 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((97 : Dyadic) * half ^ 7),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((-5 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word39Step8 :
    word39Chunk8.foldl (fun acc a => a.applyPacked acc)
      word39State8 = word39State9 := by decide +kernel

private def word39Chunk9 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word39State10 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((211 : Dyadic) * half ^ 9)⟩,
       ⟨((97 : Dyadic) * half ^ 8),
        ((39 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-7 : Dyadic) * half ^ 9)⟩,
       ⟨((-63 : Dyadic) * half ^ 8),
        ((153 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((191 : Dyadic) * half ^ 9)⟩,
       ⟨((-73 : Dyadic) * half ^ 8),
        ((-65 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-43 : Dyadic) * half ^ 7),
        ((65 : Dyadic) * half ^ 9)⟩,
       ⟨((125 : Dyadic) * half ^ 8),
        ((129 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word39Step9 :
    word39Chunk9.foldl (fun acc a => a.applyPacked acc)
      word39State9 = word39State10 := by decide +kernel

private def word39Chunk10 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word39State11 : PackedMat2 :=
    ⟨⟨⟨((121 : Dyadic) * half ^ 8),
        ((9 : Dyadic) * half ^ 9)⟩,
       ⟨((67 : Dyadic) * half ^ 8),
        ((63 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 6),
        ((-27 : Dyadic) * half ^ 8)⟩,
       ⟨((189 : Dyadic) * half ^ 8),
        ((-47 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-101 : Dyadic) * half ^ 9),
        ((201 : Dyadic) * half ^ 9)⟩,
       ⟨((-7 : Dyadic) * half ^ 9),
        ((-177 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-135 : Dyadic) * half ^ 9),
        ((-47 : Dyadic) * half ^ 7)⟩,
       ⟨((117 : Dyadic) * half ^ 9),
        ((-27 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word39Step10 :
    word39Chunk10.foldl (fun acc a => a.applyPacked acc)
      word39State10 = word39State11 := by decide +kernel

private def word39Chunk11 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word39State12 : PackedMat2 :=
    ⟨⟨⟨((-469 : Dyadic) * half ^ 10),
        ((-135 : Dyadic) * half ^ 10)⟩,
       ⟨((-135 : Dyadic) * half ^ 10),
        ((59 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-651 : Dyadic) * half ^ 10),
        ((-85 : Dyadic) * half ^ 10)⟩,
       ⟨((-321 : Dyadic) * half ^ 10),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((651 : Dyadic) * half ^ 10),
        ((85 : Dyadic) * half ^ 10)⟩,
       ⟨((-321 : Dyadic) * half ^ 10),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-469 : Dyadic) * half ^ 10),
        ((-135 : Dyadic) * half ^ 10)⟩,
       ⟨((135 : Dyadic) * half ^ 10),
        ((-59 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word39Step11 :
    word39Chunk11.foldl (fun acc a => a.applyPacked acc)
      word39State11 = word39State12 := by decide +kernel

private def word39Chunk12 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word39State13 : PackedMat2 :=
    ⟨⟨⟨((-393 : Dyadic) * half ^ 10),
        ((-21 : Dyadic) * half ^ 6)⟩,
       ⟨((11 : Dyadic) * half ^ 8),
        ((-295 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((155 : Dyadic) * half ^ 9),
        ((-209 : Dyadic) * half ^ 9)⟩,
       ⟨((-73 : Dyadic) * half ^ 10),
        ((-9 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-137 : Dyadic) * half ^ 9),
        ((383 : Dyadic) * half ^ 11)⟩,
       ⟨((281 : Dyadic) * half ^ 9),
        ((-237 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((41 : Dyadic) * half ^ 10),
        ((437 : Dyadic) * half ^ 11)⟩,
       ⟨((-631 : Dyadic) * half ^ 10),
        ((-349 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word39Step12 :
    word39Chunk12.foldl (fun acc a => a.applyPacked acc)
      word39State12 = word39State13 := by decide +kernel

private def word39Chunk13 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word39State14 : PackedMat2 :=
    ⟨⟨⟨((-27 : Dyadic) * half ^ 10),
        ((-623 : Dyadic) * half ^ 11)⟩,
       ⟨((143 : Dyadic) * half ^ 11),
        ((-1099 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((525 : Dyadic) * half ^ 11),
        ((-181 : Dyadic) * half ^ 11)⟩,
       ⟨((-245 : Dyadic) * half ^ 10),
        ((-223 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-525 : Dyadic) * half ^ 11),
        ((181 : Dyadic) * half ^ 11)⟩,
       ⟨((-245 : Dyadic) * half ^ 10),
        ((-223 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-27 : Dyadic) * half ^ 10),
        ((-623 : Dyadic) * half ^ 11)⟩,
       ⟨((-143 : Dyadic) * half ^ 11),
        ((1099 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word39Step13 :
    word39Chunk13.foldl (fun acc a => a.applyPacked acc)
      word39State13 = word39State14 := by decide +kernel

private def word39Chunk14 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word39State15 : PackedMat2 :=
    ⟨⟨⟨((-63 : Dyadic) * half ^ 7),
        ((2125 : Dyadic) * half ^ 13)⟩,
       ⟨((-1987 : Dyadic) * half ^ 12),
        ((55 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((925 : Dyadic) * half ^ 11),
        ((1853 : Dyadic) * half ^ 13)⟩,
       ⟨((-843 : Dyadic) * half ^ 12),
        ((-1145 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1499 : Dyadic) * half ^ 12),
        ((2693 : Dyadic) * half ^ 13)⟩,
       ⟨((-177 : Dyadic) * half ^ 11),
        ((-1007 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1035 : Dyadic) * half ^ 12),
        ((29 : Dyadic) * half ^ 13)⟩,
       ⟨((545 : Dyadic) * half ^ 11),
        ((-4003 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word39Step14 :
    word39Chunk14.foldl (fun acc a => a.applyPacked acc)
      word39State14 = word39State15 := by decide +kernel

private def word39Chunk15 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word39State16 : PackedMat2 :=
    ⟨⟨⟨((1279 : Dyadic) * half ^ 13),
        ((6397 : Dyadic) * half ^ 14)⟩,
       ⟨((559 : Dyadic) * half ^ 11),
        ((-6565 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1527 : Dyadic) * half ^ 13),
        ((4871 : Dyadic) * half ^ 14)⟩,
       ⟨((-255 : Dyadic) * half ^ 10),
        ((461 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-2205 : Dyadic) * half ^ 13),
        ((-3567 : Dyadic) * half ^ 14)⟩,
       ⟨((1333 : Dyadic) * half ^ 12),
        ((-513 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((6481 : Dyadic) * half ^ 13),
        ((-957 : Dyadic) * half ^ 14)⟩,
       ⟨((21 : Dyadic) * half ^ 11),
        ((-3515 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word39Step15 :
    word39Chunk15.foldl (fun acc a => a.applyPacked acc)
      word39State15 = word39State16 := by decide +kernel

private def word39Chunk16 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word39State17 : PackedMat2 :=
    ⟨⟨⟨((1317 : Dyadic) * half ^ 13),
        ((1063 : Dyadic) * half ^ 13)⟩,
       ⟨((-3663 : Dyadic) * half ^ 13),
        ((5665 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((4095 : Dyadic) * half ^ 13),
        ((4495 : Dyadic) * half ^ 14)⟩,
       ⟨((-31 : Dyadic) * half ^ 11),
        ((1839 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-8173 : Dyadic) * half ^ 14),
        ((-3971 : Dyadic) * half ^ 14)⟩,
       ⟨((-817 : Dyadic) * half ^ 14),
        ((-4219 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((7791 : Dyadic) * half ^ 14),
        ((-1173 : Dyadic) * half ^ 13)⟩,
       ⟨((-3539 : Dyadic) * half ^ 14),
        ((1245 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word39Step16 :
    word39Chunk16.foldl (fun acc a => a.applyPacked acc)
      word39State16 = word39State17 := by decide +kernel

private def word39Chunk17 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word39State18 : PackedMat2 :=
    ⟨⟨⟨((3405 : Dyadic) * half ^ 15),
        ((-3501 : Dyadic) * half ^ 14)⟩,
       ⟨((13147 : Dyadic) * half ^ 15),
        ((-9419 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((17029 : Dyadic) * half ^ 15),
        ((1083 : Dyadic) * half ^ 14)⟩,
       ⟨((12007 : Dyadic) * half ^ 15),
        ((9227 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((17029 : Dyadic) * half ^ 15),
        ((1083 : Dyadic) * half ^ 14)⟩,
       ⟨((-12007 : Dyadic) * half ^ 15),
        ((-9227 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-3405 : Dyadic) * half ^ 15),
        ((3501 : Dyadic) * half ^ 14)⟩,
       ⟨((13147 : Dyadic) * half ^ 15),
        ((-9419 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word39Step17 :
    word39Chunk17.foldl (fun acc a => a.applyPacked acc)
      word39State17 = word39State18 := by decide +kernel

private def word39Chunk18 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word39State19 : PackedMat2 :=
    ⟨⟨⟨((-5061 : Dyadic) * half ^ 15),
        ((7495 : Dyadic) * half ^ 15)⟩,
       ⟨((-1715 : Dyadic) * half ^ 12),
        ((-1541 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-1385 : Dyadic) * half ^ 13),
        ((3701 : Dyadic) * half ^ 14)⟩,
       ⟨((24315 : Dyadic) * half ^ 15),
        ((2377 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-5025 : Dyadic) * half ^ 15),
        ((29855 : Dyadic) * half ^ 16)⟩,
       ⟨((9779 : Dyadic) * half ^ 15),
        ((18775 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((2259 : Dyadic) * half ^ 13),
        ((8659 : Dyadic) * half ^ 16)⟩,
       ⟨((-2977 : Dyadic) * half ^ 14),
        ((18781 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word39Step18 :
    word39Chunk18.foldl (fun acc a => a.applyPacked acc)
      word39State18 = word39State19 := by decide +kernel

private def word39Chunk19 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word39State20 : PackedMat2 :=
    ⟨⟨⟨((23685 : Dyadic) * half ^ 16),
        ((22815 : Dyadic) * half ^ 17)⟩,
       ⟨((409 : Dyadic) * half ^ 14),
        ((6325 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-475 : Dyadic) * half ^ 16),
        ((-7175 : Dyadic) * half ^ 17)⟩,
       ⟨((-1685 : Dyadic) * half ^ 14),
        ((82215 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((1685 : Dyadic) * half ^ 14),
        ((-82215 : Dyadic) * half ^ 17)⟩,
       ⟨((475 : Dyadic) * half ^ 16),
        ((7175 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((409 : Dyadic) * half ^ 14),
        ((6325 : Dyadic) * half ^ 17)⟩,
       ⟨((23685 : Dyadic) * half ^ 16),
        ((22815 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word39Step19 :
    word39Chunk19.foldl (fun acc a => a.applyPacked acc)
      word39State19 = word39State20 := by decide +kernel

private def word39Chunk20 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word39State21 : PackedMat2 :=
    ⟨⟨⟨((14439 : Dyadic) * half ^ 17),
        ((30815 : Dyadic) * half ^ 16)⟩,
       ⟨((29535 : Dyadic) * half ^ 17),
        ((591 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2071 : Dyadic) * half ^ 17),
        ((-44745 : Dyadic) * half ^ 17)⟩,
       ⟨((58055 : Dyadic) * half ^ 17),
        ((-21735 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-4155 : Dyadic) * half ^ 13),
        ((3499 : Dyadic) * half ^ 14)⟩,
       ⟨((-11505 : Dyadic) * half ^ 16),
        ((-30063 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-35543 : Dyadic) * half ^ 16),
        ((-21987 : Dyadic) * half ^ 17)⟩,
       ⟨((-26087 : Dyadic) * half ^ 16),
        ((1887 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word39Step20 :
    word39Chunk20.foldl (fun acc a => a.applyPacked acc)
      word39State20 = word39State21 := by decide +kernel

private def word39Chunk21 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word39State22 : PackedMat2 :=
    ⟨⟨⟨((2997 : Dyadic) * half ^ 14),
        ((-2631 : Dyadic) * half ^ 15)⟩,
       ⟨((4123 : Dyadic) * half ^ 13),
        ((-37413 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-14225 : Dyadic) * half ^ 16),
        ((-135093 : Dyadic) * half ^ 18)⟩,
       ⟨((-32079 : Dyadic) * half ^ 17),
        ((13571 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((107951 : Dyadic) * half ^ 18),
        ((60529 : Dyadic) * half ^ 18)⟩,
       ⟨((162235 : Dyadic) * half ^ 18),
        ((-3629 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-58461 : Dyadic) * half ^ 18),
        ((11243 : Dyadic) * half ^ 15)⟩,
       ⟨((16365 : Dyadic) * half ^ 18),
        ((-5249 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word39Step21 :
    word39Chunk21.foldl (fun acc a => a.applyPacked acc)
      word39State21 = word39State22 := by decide +kernel

private def word39Chunk22 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word39State23 : PackedMat2 :=
    ⟨⟨⟨((182095 : Dyadic) * half ^ 19),
        ((-131501 : Dyadic) * half ^ 19)⟩,
       ⟨((288503 : Dyadic) * half ^ 19),
        ((-20771 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-59469 : Dyadic) * half ^ 19),
        ((-84169 : Dyadic) * half ^ 18)⟩,
       ⟨((-132423 : Dyadic) * half ^ 19),
        ((-75241 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-132423 : Dyadic) * half ^ 19),
        ((-75241 : Dyadic) * half ^ 18)⟩,
       ⟨((-59469 : Dyadic) * half ^ 19),
        ((-84169 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-288503 : Dyadic) * half ^ 19),
        ((20771 : Dyadic) * half ^ 19)⟩,
       ⟨((-182095 : Dyadic) * half ^ 19),
        ((131501 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word39Step22 :
    word39Chunk22.foldl (fun acc a => a.applyPacked acc)
      word39State22 = word39State23 := by decide +kernel

private def word39Chunk23 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word39State24 : PackedMat2 :=
    ⟨⟨⟨((-126257 : Dyadic) * half ^ 20),
        ((275051 : Dyadic) * half ^ 20)⟩,
       ⟨((640797 : Dyadic) * half ^ 20),
        ((34635 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((42637 : Dyadic) * half ^ 20),
        ((-134573 : Dyadic) * half ^ 20)⟩,
       ⟨((8059 : Dyadic) * half ^ 20),
        ((-243399 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-42637 : Dyadic) * half ^ 20),
        ((134573 : Dyadic) * half ^ 20)⟩,
       ⟨((8059 : Dyadic) * half ^ 20),
        ((-243399 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-126257 : Dyadic) * half ^ 20),
        ((275051 : Dyadic) * half ^ 20)⟩,
       ⟨((-640797 : Dyadic) * half ^ 20),
        ((-34635 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word39Step23 :
    word39Chunk23.foldl (fun acc a => a.applyPacked acc)
      word39State23 = word39State24 := by decide +kernel

private def word39Chunk24 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word39State25 : PackedMat2 :=
    ⟨⟨⟨((-109545 : Dyadic) * half ^ 21),
        ((-122599 : Dyadic) * half ^ 21)⟩,
       ⟨((1333039 : Dyadic) * half ^ 21),
        ((-76851 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((232467 : Dyadic) * half ^ 21),
        ((460799 : Dyadic) * half ^ 21)⟩,
       ⟨((-83385 : Dyadic) * half ^ 21),
        ((-505727 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-550655 : Dyadic) * half ^ 21),
        ((74541 : Dyadic) * half ^ 21)⟩,
       ⟨((1472253 : Dyadic) * half ^ 21),
        ((78963 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((276301 : Dyadic) * half ^ 21),
        ((-611747 : Dyadic) * half ^ 21)⟩,
       ⟨((-31103 : Dyadic) * half ^ 21),
        ((180323 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word39Step24 :
    word39Chunk24.foldl (fun acc a => a.applyPacked acc)
      word39State24 = word39State25 := by decide +kernel

private def word39Chunk25 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word39State26 : PackedMat2 :=
    ⟨⟨⟨((-584115 : Dyadic) * half ^ 21),
        ((568309 : Dyadic) * half ^ 22)⟩,
       ⟨((-139931 : Dyadic) * half ^ 21),
        ((287065 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-3993 : Dyadic) * half ^ 15),
        ((2158541 : Dyadic) * half ^ 22)⟩,
       ⟨((-323017 : Dyadic) * half ^ 20),
        ((-1429873 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((3993 : Dyadic) * half ^ 15),
        ((-2158541 : Dyadic) * half ^ 22)⟩,
       ⟨((-323017 : Dyadic) * half ^ 20),
        ((-1429873 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-584115 : Dyadic) * half ^ 21),
        ((568309 : Dyadic) * half ^ 22)⟩,
       ⟨((139931 : Dyadic) * half ^ 21),
        ((-287065 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word39Step25 :
    word39Chunk25.foldl (fun acc a => a.applyPacked acc)
      word39State25 = word39State26 := by decide +kernel

private def word39Chunk26 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word39State27 : PackedMat2 :=
    ⟨⟨⟨((280055 : Dyadic) * half ^ 20),
        ((-3458099 : Dyadic) * half ^ 23)⟩,
       ⟨((-662531 : Dyadic) * half ^ 22),
        ((-1872675 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1055839 : Dyadic) * half ^ 21),
        ((230123 : Dyadic) * half ^ 23)⟩,
       ⟨((894747 : Dyadic) * half ^ 22),
        ((2399763 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-271205 : Dyadic) * half ^ 20),
        ((1216931 : Dyadic) * half ^ 23)⟩,
       ⟨((-1314943 : Dyadic) * half ^ 22),
        ((-3006425 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((99089 : Dyadic) * half ^ 19),
        ((-1782751 : Dyadic) * half ^ 23)⟩,
       ⟨((-2665387 : Dyadic) * half ^ 22),
        ((457689 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word39Step26 :
    word39Chunk26.foldl (fun acc a => a.applyPacked acc)
      word39State26 = word39State27 := by decide +kernel

private def word39Chunk27 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word39State28 : PackedMat2 :=
    ⟨⟨⟨((-2453623 : Dyadic) * half ^ 22),
        ((242687 : Dyadic) * half ^ 20)⟩,
       ⟨((35573 : Dyadic) * half ^ 21),
        ((-1191699 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((113899 : Dyadic) * half ^ 21),
        ((-817253 : Dyadic) * half ^ 23)⟩,
       ⟨((1293493 : Dyadic) * half ^ 21),
        ((973073 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1293493 : Dyadic) * half ^ 21),
        ((973073 : Dyadic) * half ^ 22)⟩,
       ⟨((113899 : Dyadic) * half ^ 21),
        ((-817253 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-35573 : Dyadic) * half ^ 21),
        ((1191699 : Dyadic) * half ^ 23)⟩,
       ⟨((2453623 : Dyadic) * half ^ 22),
        ((-242687 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word39Step27 :
    word39Chunk27.foldl (fun acc a => a.applyPacked acc)
      word39State27 = word39State28 := by decide +kernel

private def word39Chunk28 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word39State29 : PackedMat2 :=
    ⟨⟨⟨((13072121 : Dyadic) * half ^ 24),
        ((-332105 : Dyadic) * half ^ 22)⟩,
       ⟨((-3844145 : Dyadic) * half ^ 24),
        ((-66535 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-8535259 : Dyadic) * half ^ 24),
        ((-1148191 : Dyadic) * half ^ 23)⟩,
       ⟨((1317763 : Dyadic) * half ^ 24),
        ((-1890111 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((4186493 : Dyadic) * half ^ 24),
        ((902187 : Dyadic) * half ^ 22)⟩,
       ⟨((406271 : Dyadic) * half ^ 24),
        ((4926511 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1394955 : Dyadic) * half ^ 24),
        ((1153497 : Dyadic) * half ^ 22)⟩,
       ⟨((-1261885 : Dyadic) * half ^ 24),
        ((8458133 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word39Step28 :
    word39Chunk28.foldl (fun acc a => a.applyPacked acc)
      word39State28 = word39State29 := by decide +kernel

private def word39Chunk29 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word39State30 : PackedMat2 :=
    ⟨⟨⟨((-3673977 : Dyadic) * half ^ 24),
        ((5421137 : Dyadic) * half ^ 24)⟩,
       ⟨((1452661 : Dyadic) * half ^ 22),
        ((-1641227 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-2372831 : Dyadic) * half ^ 22),
        ((-664591 : Dyadic) * half ^ 22)⟩,
       ⟨((-8079813 : Dyadic) * half ^ 24),
        ((-522577 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-2372831 : Dyadic) * half ^ 22),
        ((-664591 : Dyadic) * half ^ 22)⟩,
       ⟨((8079813 : Dyadic) * half ^ 24),
        ((522577 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((3673977 : Dyadic) * half ^ 24),
        ((-5421137 : Dyadic) * half ^ 24)⟩,
       ⟨((1452661 : Dyadic) * half ^ 22),
        ((-1641227 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word39Step29 :
    word39Chunk29.foldl (fun acc a => a.applyPacked acc)
      word39State29 = word39State30 := by decide +kernel

private def word39Chunk30 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word39State31 : PackedMat2 :=
    ⟨⟨⟨((8212571 : Dyadic) * half ^ 25),
        ((13505637 : Dyadic) * half ^ 26)⟩,
       ⟨((-1205161 : Dyadic) * half ^ 23),
        ((23875073 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((6542995 : Dyadic) * half ^ 25),
        ((-15800827 : Dyadic) * half ^ 26)⟩,
       ⟨((-1737057 : Dyadic) * half ^ 24),
        ((-30960975 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-1737057 : Dyadic) * half ^ 24),
        ((-30960975 : Dyadic) * half ^ 26)⟩,
       ⟨((6542995 : Dyadic) * half ^ 25),
        ((-15800827 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((1205161 : Dyadic) * half ^ 23),
        ((-23875073 : Dyadic) * half ^ 26)⟩,
       ⟨((-8212571 : Dyadic) * half ^ 25),
        ((-13505637 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word39Step30 :
    word39Chunk30.foldl (fun acc a => a.applyPacked acc)
      word39State30 = word39State31 := by decide +kernel

private def word39Chunk31 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word39State32 : PackedMat2 :=
    ⟨⟨⟨((-15978773 : Dyadic) * half ^ 25),
        ((-10639307 : Dyadic) * half ^ 26)⟩,
       ⟨((9825911 : Dyadic) * half ^ 24),
        ((189975 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-7089581 : Dyadic) * half ^ 25),
        ((6673373 : Dyadic) * half ^ 24)⟩,
       ⟨((-4089537 : Dyadic) * half ^ 25),
        ((2597907 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((4089537 : Dyadic) * half ^ 25),
        ((-2597907 : Dyadic) * half ^ 26)⟩,
       ⟨((7089581 : Dyadic) * half ^ 25),
        ((-6673373 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((9825911 : Dyadic) * half ^ 24),
        ((189975 : Dyadic) * half ^ 23)⟩,
       ⟨((-15978773 : Dyadic) * half ^ 25),
        ((-10639307 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word39Step31 :
    word39Chunk31.foldl (fun acc a => a.applyPacked acc)
      word39State31 = word39State32 := by decide +kernel

private def word39Chunk32 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word39State33 : PackedMat2 :=
    ⟨⟨⟨((-94559859 : Dyadic) * half ^ 27),
        ((9103717 : Dyadic) * half ^ 26)⟩,
       ⟨((27684279 : Dyadic) * half ^ 27),
        ((23913181 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((55248857 : Dyadic) * half ^ 27),
        ((11777887 : Dyadic) * half ^ 26)⟩,
       ⟨((-7150177 : Dyadic) * half ^ 27),
        ((33811243 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((55248857 : Dyadic) * half ^ 27),
        ((11777887 : Dyadic) * half ^ 26)⟩,
       ⟨((7150177 : Dyadic) * half ^ 27),
        ((-33811243 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((94559859 : Dyadic) * half ^ 27),
        ((-9103717 : Dyadic) * half ^ 26)⟩,
       ⟨((27684279 : Dyadic) * half ^ 27),
        ((23913181 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word39Step32 :
    word39Chunk32.foldl (fun acc a => a.applyPacked acc)
      word39State32 = word39State33 := by decide +kernel

private def word39Chunk33 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word39State34 : PackedMat2 :=
    ⟨⟨⟨((55758469 : Dyadic) * half ^ 28),
        ((27941181 : Dyadic) * half ^ 27)⟩,
       ⟨((141234971 : Dyadic) * half ^ 28),
        ((-55741605 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((94322565 : Dyadic) * half ^ 28),
        ((-5212821 : Dyadic) * half ^ 26)⟩,
       ⟨((62955171 : Dyadic) * half ^ 28),
        ((106798147 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-85946863 : Dyadic) * half ^ 28),
        ((-19659717 : Dyadic) * half ^ 26)⟩,
       ⟨((127649431 : Dyadic) * half ^ 28),
        ((-15683697 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((140757 : Dyadic) * half ^ 28),
        ((6156045 : Dyadic) * half ^ 24)⟩,
       ⟨((111623967 : Dyadic) * half ^ 28),
        ((-42738251 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word39Step33 :
    word39Chunk33.foldl (fun acc a => a.applyPacked acc)
      word39State33 = word39State34 := by decide +kernel

private def word39Chunk34 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word39State35 : PackedMat2 :=
    ⟨⟨⟨((8371231 : Dyadic) * half ^ 27),
        ((218298221 : Dyadic) * half ^ 29)⟩,
       ⟨((603091 : Dyadic) * half ^ 23),
        ((176266049 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-122946355 : Dyadic) * half ^ 28),
        ((43266023 : Dyadic) * half ^ 29)⟩,
       ⟨((126080195 : Dyadic) * half ^ 28),
        ((-13778475 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-122946355 : Dyadic) * half ^ 28),
        ((43266023 : Dyadic) * half ^ 29)⟩,
       ⟨((-126080195 : Dyadic) * half ^ 28),
        ((13778475 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-8371231 : Dyadic) * half ^ 27),
        ((-218298221 : Dyadic) * half ^ 29)⟩,
       ⟨((603091 : Dyadic) * half ^ 23),
        ((176266049 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word39Step34 :
    word39Chunk34.foldl (fun acc a => a.applyPacked acc)
      word39State34 = word39State35 := by decide +kernel

private def word39Chunk35 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word39State36 : PackedMat2 :=
    ⟨⟨⟨((-202315 : Dyadic) * half ^ 22),
        ((525189 : Dyadic) * half ^ 23)⟩,
       ⟨((190085433 : Dyadic) * half ^ 29),
        ((-16447549 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-90191391 : Dyadic) * half ^ 29),
        ((-35899223 : Dyadic) * half ^ 26)⟩,
       ⟨((125150655 : Dyadic) * half ^ 28),
        ((-75025969 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((90191391 : Dyadic) * half ^ 29),
        ((35899223 : Dyadic) * half ^ 26)⟩,
       ⟨((125150655 : Dyadic) * half ^ 28),
        ((-75025969 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-202315 : Dyadic) * half ^ 22),
        ((525189 : Dyadic) * half ^ 23)⟩,
       ⟨((-190085433 : Dyadic) * half ^ 29),
        ((16447549 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word39Step35 :
    word39Chunk35.foldl (fun acc a => a.applyPacked acc)
      word39State35 = word39State36 := by decide +kernel

private def word39Chunk36 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word39State37 : PackedMat2 :=
    ⟨⟨⟨((-489082443 : Dyadic) * half ^ 30),
        ((-71851421 : Dyadic) * half ^ 29)⟩,
       ⟨((709003771 : Dyadic) * half ^ 30),
        ((33126425 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((395606601 : Dyadic) * half ^ 30),
        ((-292152965 : Dyadic) * half ^ 30)⟩,
       ⟨((12954173 : Dyadic) * half ^ 30),
        ((-129565667 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((52714829 : Dyadic) * half ^ 27),
        ((-204280387 : Dyadic) * half ^ 30)⟩,
       ⟨((81293649 : Dyadic) * half ^ 29),
        ((-95663107 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-9681249 : Dyadic) * half ^ 27),
        ((13745083 : Dyadic) * half ^ 27)⟩,
       ⟨((-52488923 : Dyadic) * half ^ 28),
        ((-599043107 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word39Step36 :
    word39Chunk36.foldl (fun acc a => a.applyPacked acc)
      word39State36 = word39State37 := by decide +kernel

private def word39Chunk37 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word39State38 : PackedMat2 :=
    ⟨⟨⟨((118626219 : Dyadic) * half ^ 31),
        ((-250605199 : Dyadic) * half ^ 31)⟩,
       ⟨((-261158217 : Dyadic) * half ^ 31),
        ((240360325 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((1009107647 : Dyadic) * half ^ 31),
        ((-217174885 : Dyadic) * half ^ 30)⟩,
       ⟨((-1637857579 : Dyadic) * half ^ 31),
        ((-40510703 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-1637857579 : Dyadic) * half ^ 31),
        ((-40510703 : Dyadic) * half ^ 28)⟩,
       ⟨((1009107647 : Dyadic) * half ^ 31),
        ((-217174885 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((261158217 : Dyadic) * half ^ 31),
        ((-240360325 : Dyadic) * half ^ 31)⟩,
       ⟨((-118626219 : Dyadic) * half ^ 31),
        ((250605199 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word39Step37 :
    word39Chunk37.foldl (fun acc a => a.applyPacked acc)
      word39State37 = word39State38 := by decide +kernel

private def word39Chunk38 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word39State39 : PackedMat2 :=
    ⟨⟨⟨((-1986291105 : Dyadic) * half ^ 32),
        ((-30987133 : Dyadic) * half ^ 30)⟩,
       ⟨((1378647209 : Dyadic) * half ^ 32),
        ((-996581293 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((779644003 : Dyadic) * half ^ 32),
        ((920778841 : Dyadic) * half ^ 31)⟩,
       ⟨((1769903613 : Dyadic) * half ^ 32),
        ((-174033913 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1667523769 : Dyadic) * half ^ 32),
        ((-79673363 : Dyadic) * half ^ 28)⟩,
       ⟨((-2015591595 : Dyadic) * half ^ 32),
        ((495129805 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1120529825 : Dyadic) * half ^ 32),
        ((-75955487 : Dyadic) * half ^ 30)⟩,
       ⟨((872632761 : Dyadic) * half ^ 32),
        ((-1682469157 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word39Step38 :
    word39Chunk38.foldl (fun acc a => a.applyPacked acc)
      word39State38 = word39State39 := by decide +kernel

private def word39Chunk39 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word39State40 : PackedMat2 :=
    ⟨⟨⟨((-601547069 : Dyadic) * half ^ 31),
        ((-1415633747 : Dyadic) * half ^ 32)⟩,
       ⟨((-1104775039 : Dyadic) * half ^ 32),
        ((270166191 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-36539677 : Dyadic) * half ^ 32),
        ((103716173 : Dyadic) * half ^ 30)⟩,
       ⟨((-118383879 : Dyadic) * half ^ 30),
        ((1152010647 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-36539677 : Dyadic) * half ^ 32),
        ((103716173 : Dyadic) * half ^ 30)⟩,
       ⟨((118383879 : Dyadic) * half ^ 30),
        ((-1152010647 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((601547069 : Dyadic) * half ^ 31),
        ((1415633747 : Dyadic) * half ^ 32)⟩,
       ⟨((-1104775039 : Dyadic) * half ^ 32),
        ((270166191 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word39Step39 :
    word39Chunk39.foldl (fun acc a => a.applyPacked acc)
      word39State39 = word39State40 := by decide +kernel

private def word39Chunk40 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word39State41 : PackedMat2 :=
    ⟨⟨⟨((992393531 : Dyadic) * half ^ 33),
        ((-3996928233 : Dyadic) * half ^ 34)⟩,
       ⟨((-251448247 : Dyadic) * half ^ 30),
        ((-4603821733 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((2178566265 : Dyadic) * half ^ 33),
        ((-2373252765 : Dyadic) * half ^ 34)⟩,
       ⟨((407966815 : Dyadic) * half ^ 29),
        ((-19022549 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((407966815 : Dyadic) * half ^ 29),
        ((-19022549 : Dyadic) * half ^ 34)⟩,
       ⟨((2178566265 : Dyadic) * half ^ 33),
        ((-2373252765 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((251448247 : Dyadic) * half ^ 30),
        ((4603821733 : Dyadic) * half ^ 34)⟩,
       ⟨((-992393531 : Dyadic) * half ^ 33),
        ((3996928233 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word39Step40 :
    word39Chunk40.foldl (fun acc a => a.applyPacked acc)
      word39State40 = word39State41 := by decide +kernel

private def word39Chunk41 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word39State42 : PackedMat2 :=
    ⟨⟨⟨((1609816943 : Dyadic) * half ^ 32),
        ((6046521883 : Dyadic) * half ^ 35)⟩,
       ⟨((-11161906623 : Dyadic) * half ^ 34),
        ((671205493 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((1499230227 : Dyadic) * half ^ 32),
        ((-5760548513 : Dyadic) * half ^ 35)⟩,
       ⟨((288161711 : Dyadic) * half ^ 34),
        ((10765876397 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-288161711 : Dyadic) * half ^ 34),
        ((-10765876397 : Dyadic) * half ^ 35)⟩,
       ⟨((-1499230227 : Dyadic) * half ^ 32),
        ((5760548513 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-11161906623 : Dyadic) * half ^ 34),
        ((671205493 : Dyadic) * half ^ 35)⟩,
       ⟨((1609816943 : Dyadic) * half ^ 32),
        ((6046521883 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word39Step41 :
    word39Chunk41.foldl (fun acc a => a.applyPacked acc)
      word39State41 = word39State42 := by decide +kernel

private def word39Chunk42 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word39State43 : PackedMat2 :=
    ⟨⟨⟨((17496590217 : Dyadic) * half ^ 35),
        ((1435825403 : Dyadic) * half ^ 32)⟩,
       ⟨((13107394173 : Dyadic) * half ^ 35),
        ((-5509459969 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((5113196399 : Dyadic) * half ^ 35),
        ((278379963 : Dyadic) * half ^ 35)⟩,
       ⟨((10323529533 : Dyadic) * half ^ 35),
        ((-5615373487 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-1334248381 : Dyadic) * half ^ 33),
        ((3859181483 : Dyadic) * half ^ 34)⟩,
       ⟨((2946876725 : Dyadic) * half ^ 34),
        ((-2605166567 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-233841643 : Dyadic) * half ^ 34),
        ((-15301992195 : Dyadic) * half ^ 35)⟩,
       ⟨((-11252761581 : Dyadic) * half ^ 34),
        ((-1097299011 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word39Step42 :
    word39Chunk42.foldl (fun acc a => a.applyPacked acc)
      word39State42 = word39State43 := by decide +kernel

private def word39Chunk43 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word39State44 : PackedMat2 :=
    ⟨⟨⟨((15202805799 : Dyadic) * half ^ 36),
        ((20797147189 : Dyadic) * half ^ 36)⟩,
       ⟨((-10435003109 : Dyadic) * half ^ 36),
        ((6799790991 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-9299086321 : Dyadic) * half ^ 36),
        ((26030562081 : Dyadic) * half ^ 36)⟩,
       ⟨((16387972587 : Dyadic) * half ^ 36),
        ((6398253759 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((9299086321 : Dyadic) * half ^ 36),
        ((-26030562081 : Dyadic) * half ^ 36)⟩,
       ⟨((16387972587 : Dyadic) * half ^ 36),
        ((6398253759 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((15202805799 : Dyadic) * half ^ 36),
        ((20797147189 : Dyadic) * half ^ 36)⟩,
       ⟨((10435003109 : Dyadic) * half ^ 36),
        ((-6799790991 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word39Step43 :
    word39Chunk43.foldl (fun acc a => a.applyPacked acc)
      word39State43 = word39State44 := by decide +kernel

private def word39Chunk44 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word39State45 : PackedMat2 :=
    ⟨⟨⟨((-76829364845 : Dyadic) * half ^ 37),
        ((23703729877 : Dyadic) * half ^ 37)⟩,
       ⟨((11085138823 : Dyadic) * half ^ 37),
        ((25626730917 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((72360298411 : Dyadic) * half ^ 37),
        ((18003844363 : Dyadic) * half ^ 37)⟩,
       ⟨((2889009451 : Dyadic) * half ^ 37),
        ((-8614160005 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((775524353 : Dyadic) * half ^ 37),
        ((37624653931 : Dyadic) * half ^ 37)⟩,
       ⟨((35232164373 : Dyadic) * half ^ 37),
        ((542744445 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-74957191711 : Dyadic) * half ^ 37),
        ((32872113011 : Dyadic) * half ^ 37)⟩,
       ⟨((27549731957 : Dyadic) * half ^ 37),
        ((21978625917 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word39Step44 :
    word39Chunk44.foldl (fun acc a => a.applyPacked acc)
      word39State44 = word39State45 := by decide +kernel

private def word39Chunk45 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word39State46 : PackedMat2 :=
    ⟨⟨⟨((54341309671 : Dyadic) * half ^ 37),
        ((-27519745579 : Dyadic) * half ^ 36)⟩,
       ⟨((5697137343 : Dyadic) * half ^ 36),
        ((26008594355 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((13743505515 : Dyadic) * half ^ 35),
        ((2058902767 : Dyadic) * half ^ 33)⟩,
       ⟨((24494398607 : Dyadic) * half ^ 37),
        ((563643091 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-13743505515 : Dyadic) * half ^ 35),
        ((-2058902767 : Dyadic) * half ^ 33)⟩,
       ⟨((24494398607 : Dyadic) * half ^ 37),
        ((563643091 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((54341309671 : Dyadic) * half ^ 37),
        ((-27519745579 : Dyadic) * half ^ 36)⟩,
       ⟨((-5697137343 : Dyadic) * half ^ 36),
        ((-26008594355 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word39Step45 :
    word39Chunk45.foldl (fun acc a => a.applyPacked acc)
      word39State45 = word39State46 := by decide +kernel

private def word39Chunk46 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word39State47 : PackedMat2 :=
    ⟨⟨⟨((-59171271725 : Dyadic) * half ^ 37),
        ((26185807179 : Dyadic) * half ^ 39)⟩,
       ⟨((175374100477 : Dyadic) * half ^ 38),
        ((-7822012277 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-4957199447 : Dyadic) * half ^ 35),
        ((80748763457 : Dyadic) * half ^ 39)⟩,
       ⟨((156151234511 : Dyadic) * half ^ 38),
        ((49138101401 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((3951332757 : Dyadic) * half ^ 36),
        ((-195808830087 : Dyadic) * half ^ 39)⟩,
       ⟨((-64943432429 : Dyadic) * half ^ 38),
        ((-116493638935 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-531372179 : Dyadic) * half ^ 33),
        ((293716643927 : Dyadic) * half ^ 39)⟩,
       ⟨((9181897451 : Dyadic) * half ^ 38),
        ((57031557027 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word39Step46 :
    word39Chunk46.foldl (fun acc a => a.applyPacked acc)
      word39State46 = word39State47 := by decide +kernel

private def word39Chunk47 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word39State48 : PackedMat2 :=
    ⟨⟨⟨((93570226039 : Dyadic) * half ^ 39),
        ((16848248811 : Dyadic) * half ^ 37)⟩,
       ⟨((168525745657 : Dyadic) * half ^ 39),
        ((-208299361417 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-289157025933 : Dyadic) * half ^ 39),
        ((-21238605057 : Dyadic) * half ^ 38)⟩,
       ⟨((273295199261 : Dyadic) * half ^ 39),
        ((60430054031 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-289157025933 : Dyadic) * half ^ 39),
        ((-21238605057 : Dyadic) * half ^ 38)⟩,
       ⟨((-273295199261 : Dyadic) * half ^ 39),
        ((-60430054031 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-93570226039 : Dyadic) * half ^ 39),
        ((-16848248811 : Dyadic) * half ^ 37)⟩,
       ⟨((168525745657 : Dyadic) * half ^ 39),
        ((-208299361417 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word39Step47 :
    word39Chunk47.foldl (fun acc a => a.applyPacked acc)
      word39State47 = word39State48 := by decide +kernel

private def word39Chunk48 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word39State49 : PackedMat2 :=
    ⟨⟨⟨((291336381215 : Dyadic) * half ^ 40),
        ((-388225960763 : Dyadic) * half ^ 40)⟩,
       ⟨((-88534751815 : Dyadic) * half ^ 40),
        ((-26409275263 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-201183466947 : Dyadic) * half ^ 40),
        ((-593528581619 : Dyadic) * half ^ 40)⟩,
       ⟨((179450370831 : Dyadic) * half ^ 40),
        ((-10905763061 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((680774686107 : Dyadic) * half ^ 40),
        ((5433274029 : Dyadic) * half ^ 39)⟩,
       ⟨((506282477131 : Dyadic) * half ^ 40),
        ((190316918889 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-493863061815 : Dyadic) * half ^ 40),
        ((25350203675 : Dyadic) * half ^ 38)⟩,
       ⟨((-282588859711 : Dyadic) * half ^ 40),
        ((189935566515 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word39Step48 :
    word39Chunk48.foldl (fun acc a => a.applyPacked acc)
      word39State48 = word39State49 := by decide +kernel

private def word39Chunk49 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word39State50 : PackedMat2 :=
    ⟨⟨⟨((-15889587465 : Dyadic) * half ^ 36),
        ((309727377779 : Dyadic) * half ^ 41)⟩,
       ⟨((-30280321959 : Dyadic) * half ^ 39),
        ((-1070289294197 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-638986391127 : Dyadic) * half ^ 40),
        ((-8300261407 : Dyadic) * half ^ 41)⟩,
       ⟨((-333506028569 : Dyadic) * half ^ 40),
        ((-25852250025 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-638986391127 : Dyadic) * half ^ 40),
        ((-8300261407 : Dyadic) * half ^ 41)⟩,
       ⟨((333506028569 : Dyadic) * half ^ 40),
        ((25852250025 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((15889587465 : Dyadic) * half ^ 36),
        ((-309727377779 : Dyadic) * half ^ 41)⟩,
       ⟨((-30280321959 : Dyadic) * half ^ 39),
        ((-1070289294197 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word39Step49 :
    word39Chunk49.foldl (fun acc a => a.applyPacked acc)
      word39State49 = word39State50 := by decide +kernel

private def word39Chunk50 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word39State51 : PackedMat2 :=
    ⟨⟨⟨((365815988219 : Dyadic) * half ^ 41),
        ((558588899489 : Dyadic) * half ^ 42)⟩,
       ⟨((-120223842581 : Dyadic) * half ^ 40),
        ((1091074878643 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1235501813445 : Dyadic) * half ^ 41),
        ((-581055228905 : Dyadic) * half ^ 42)⟩,
       ⟨((-23944828887 : Dyadic) * half ^ 37),
        ((-2025229725275 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-722087248185 : Dyadic) * half ^ 41),
        ((-1618619075637 : Dyadic) * half ^ 42)⟩,
       ⟨((-651571238545 : Dyadic) * half ^ 40),
        ((852384551253 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-266242989577 : Dyadic) * half ^ 41),
        ((606263673381 : Dyadic) * half ^ 42)⟩,
       ⟨((-412415944533 : Dyadic) * half ^ 40),
        ((-125368303057 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word39Step50 :
    word39Chunk50.foldl (fun acc a => a.applyPacked acc)
      word39State50 = word39State51 := by decide +kernel

private def word39Chunk51 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word39State52 : PackedMat2 :=
    ⟨⟨⟨((415919322459 : Dyadic) * half ^ 42),
        ((-298084078435 : Dyadic) * half ^ 40)⟩,
       ⟨((2692392680307 : Dyadic) * half ^ 42),
        ((-125840424935 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((42509718449 : Dyadic) * half ^ 42),
        ((1702579236761 : Dyadic) * half ^ 42)⟩,
       ⟨((-1155543900049 : Dyadic) * half ^ 42),
        ((-952939326389 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1155543900049 : Dyadic) * half ^ 42),
        ((952939326389 : Dyadic) * half ^ 42)⟩,
       ⟨((-42509718449 : Dyadic) * half ^ 42),
        ((-1702579236761 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((2692392680307 : Dyadic) * half ^ 42),
        ((-125840424935 : Dyadic) * half ^ 41)⟩,
       ⟨((415919322459 : Dyadic) * half ^ 42),
        ((-298084078435 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word39Step51 :
    word39Chunk51.foldl (fun acc a => a.applyPacked acc)
      word39State51 = word39State52 := by decide +kernel

private def word39Chunk52 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word39State53 : PackedMat2 :=
    ⟨⟨⟨((-4327425397415 : Dyadic) * half ^ 43),
        ((111083081529 : Dyadic) * half ^ 43)⟩,
       ⟨((2568076185869 : Dyadic) * half ^ 43),
        ((262385396977 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((6004719537181 : Dyadic) * half ^ 43),
        ((-558706956545 : Dyadic) * half ^ 43)⟩,
       ⟨((-922713470459 : Dyadic) * half ^ 43),
        ((421318003909 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((1126565059091 : Dyadic) * half ^ 43),
        ((2541003033361 : Dyadic) * half ^ 43)⟩,
       ⟨((-2243978972181 : Dyadic) * half ^ 43),
        ((865929125955 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-2210166257345 : Dyadic) * half ^ 43),
        ((879674605773 : Dyadic) * half ^ 43)⟩,
       ⟨((1988000094287 : Dyadic) * half ^ 43),
        ((1723875395821 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word39Step52 :
    word39Chunk52.foldl (fun acc a => a.applyPacked acc)
      word39State52 = word39State53 := by decide +kernel

private def word39Chunk53 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word39State54 : PackedMat2 :=
    ⟨⟨⟨((-2905950192515 : Dyadic) * half ^ 43),
        ((-5408677733421 : Dyadic) * half ^ 44)⟩,
       ⟨((1236314927461 : Dyadic) * half ^ 43),
        ((2194200545167 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((2566041081019 : Dyadic) * half ^ 42),
        ((-582650544593 : Dyadic) * half ^ 44)⟩,
       ⟨((667248118077 : Dyadic) * half ^ 41),
        ((-5784902236371 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((-2566041081019 : Dyadic) * half ^ 42),
        ((582650544593 : Dyadic) * half ^ 44)⟩,
       ⟨((667248118077 : Dyadic) * half ^ 41),
        ((-5784902236371 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((-2905950192515 : Dyadic) * half ^ 43),
        ((-5408677733421 : Dyadic) * half ^ 44)⟩,
       ⟨((-1236314927461 : Dyadic) * half ^ 43),
        ((-2194200545167 : Dyadic) * half ^ 44)⟩⟩⟩
private lemma word39Step53 :
    word39Chunk53.foldl (fun acc a => a.applyPacked acc)
      word39State53 = word39State54 := by decide +kernel

private def word39Chunk54 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word39State55 : PackedMat2 :=
    ⟨⟨⟨((-3631943018139 : Dyadic) * half ^ 43),
        ((-345137387129 : Dyadic) * half ^ 45)⟩,
       ⟨((-3080511241795 : Dyadic) * half ^ 44),
        ((-15057415780013 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-2026474745243 : Dyadic) * half ^ 42),
        ((3421964737273 : Dyadic) * half ^ 45)⟩,
       ⟨((-1957001628213 : Dyadic) * half ^ 44),
        ((10809125780957 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-1846790260921 : Dyadic) * half ^ 43),
        ((-6148897352759 : Dyadic) * half ^ 45)⟩,
       ⟨((-7115545259115 : Dyadic) * half ^ 44),
        ((10062900609185 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-3678069598221 : Dyadic) * half ^ 43),
        ((4183374794483 : Dyadic) * half ^ 45)⟩,
       ⟨((-7701276583571 : Dyadic) * half ^ 44),
        ((-10344397278073 : Dyadic) * half ^ 45)⟩⟩⟩
private lemma word39Step54 :
    word39Chunk54.foldl (fun acc a => a.applyPacked acc)
      word39State54 = word39State55 := by decide +kernel

private def word39Chunk55 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word39State56 : PackedMat2 :=
    ⟨⟨⟨((5420636417819 : Dyadic) * half ^ 44),
        ((-361540128727 : Dyadic) * half ^ 43)⟩,
       ⟨((-3034787930563 : Dyadic) * half ^ 42),
        ((2151482955119 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((-235614958849 : Dyadic) * half ^ 42),
        ((-13683030565015 : Dyadic) * half ^ 45)⟩,
       ⟨((1445934510445 : Dyadic) * half ^ 43),
        ((3641344315215 : Dyadic) * half ^ 44)⟩⟩,
     ⟨⟨((1445934510445 : Dyadic) * half ^ 43),
        ((3641344315215 : Dyadic) * half ^ 44)⟩,
       ⟨((-235614958849 : Dyadic) * half ^ 42),
        ((-13683030565015 : Dyadic) * half ^ 45)⟩⟩,
     ⟨⟨((3034787930563 : Dyadic) * half ^ 42),
        ((-2151482955119 : Dyadic) * half ^ 45)⟩,
       ⟨((-5420636417819 : Dyadic) * half ^ 44),
        ((361540128727 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word39Step55 :
    word39Chunk55.foldl (fun acc a => a.applyPacked acc)
      word39State55 = word39State56 := by decide +kernel

private def word39Chunk56 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word39State57 : PackedMat2 :=
    ⟨⟨⟨((15623125180619 : Dyadic) * half ^ 46),
        ((12068577165145 : Dyadic) * half ^ 45)⟩,
       ⟨((33939979049561 : Dyadic) * half ^ 46),
        ((-23999189339475 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((-586234121929 : Dyadic) * half ^ 46),
        ((103632530795 : Dyadic) * half ^ 44)⟩,
       ⟨((-24910272482795 : Dyadic) * half ^ 46),
        ((-17570149495043 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((17155619371863 : Dyadic) * half ^ 46),
        ((6374126651181 : Dyadic) * half ^ 45)⟩,
       ⟨((-17984679618223 : Dyadic) * half ^ 46),
        ((-12162019180433 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((137964990815 : Dyadic) * half ^ 46),
        ((12390776057545 : Dyadic) * half ^ 45)⟩,
       ⟨((48136343669765 : Dyadic) * half ^ 46),
        ((-9158426934471 : Dyadic) * half ^ 46)⟩⟩⟩
private lemma word39Step56 :
    word39Chunk56.foldl (fun acc a => a.applyPacked acc)
      word39State56 = word39State57 := by decide +kernel

private def word39Chunk57 : List Letter := [.t, .h, .s]
private def word39State58 : PackedMat2 :=
    ⟨⟨⟨((41707303825333 : Dyadic) * half ^ 46),
        ((20266698831707 : Dyadic) * half ^ 46)⟩,
       ⟨((-24413719462655 : Dyadic) * half ^ 46),
        ((17263106585745 : Dyadic) * half ^ 46)⟩⟩,
     ⟨⟨((-23584659216295 : Dyadic) * half ^ 46),
        ((2084609057977 : Dyadic) * half ^ 43)⟩,
       ⟨((6567004835247 : Dyadic) * half ^ 46),
        ((-290223353193 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((23584659216295 : Dyadic) * half ^ 46),
        ((-2084609057977 : Dyadic) * half ^ 43)⟩,
       ⟨((6567004835247 : Dyadic) * half ^ 46),
        ((-290223353193 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((41707303825333 : Dyadic) * half ^ 46),
        ((20266698831707 : Dyadic) * half ^ 46)⟩,
       ⟨((24413719462655 : Dyadic) * half ^ 46),
        ((-17263106585745 : Dyadic) * half ^ 46)⟩⟩⟩
private lemma word39Step57 :
    word39Chunk57.foldl (fun acc a => a.applyPacked acc)
      word39State57 = word39State58 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word39_check : check word39 39 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word39 = word39State58.toMatrix := by
    unfold evalRingPacked
    change ((
      word39Chunk0 ++ word39Chunk1 ++ word39Chunk2 ++ word39Chunk3 ++
      word39Chunk4 ++ word39Chunk5 ++ word39Chunk6 ++ word39Chunk7 ++
      word39Chunk8 ++ word39Chunk9 ++ word39Chunk10 ++ word39Chunk11 ++
      word39Chunk12 ++ word39Chunk13 ++ word39Chunk14 ++ word39Chunk15 ++
      word39Chunk16 ++ word39Chunk17 ++ word39Chunk18 ++ word39Chunk19 ++
      word39Chunk20 ++ word39Chunk21 ++ word39Chunk22 ++ word39Chunk23 ++
      word39Chunk24 ++ word39Chunk25 ++ word39Chunk26 ++ word39Chunk27 ++
      word39Chunk28 ++ word39Chunk29 ++ word39Chunk30 ++ word39Chunk31 ++
      word39Chunk32 ++ word39Chunk33 ++ word39Chunk34 ++ word39Chunk35 ++
      word39Chunk36 ++ word39Chunk37 ++ word39Chunk38 ++ word39Chunk39 ++
      word39Chunk40 ++ word39Chunk41 ++ word39Chunk42 ++ word39Chunk43 ++
      word39Chunk44 ++ word39Chunk45 ++ word39Chunk46 ++ word39Chunk47 ++
      word39Chunk48 ++ word39Chunk49 ++ word39Chunk50 ++ word39Chunk51 ++
      word39Chunk52 ++ word39Chunk53 ++ word39Chunk54 ++ word39Chunk55 ++
      word39Chunk56 ++ word39Chunk57
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word39Step0, word39Step1, word39Step2, word39Step3, word39Step4,
      word39Step5, word39Step6, word39Step7, word39Step8, word39Step9,
      word39Step10, word39Step11, word39Step12, word39Step13, word39Step14,
      word39Step15, word39Step16, word39Step17, word39Step18, word39Step19,
      word39Step20, word39Step21, word39Step22, word39Step23, word39Step24,
      word39Step25, word39Step26, word39Step27, word39Step28, word39Step29,
      word39Step30, word39Step31, word39Step32, word39Step33, word39Step34,
      word39Step35, word39Step36, word39Step37, word39Step38, word39Step39,
      word39Step40, word39Step41, word39Step42, word39Step43, word39Step44,
      word39Step45, word39Step46, word39Step47, word39Step48, word39Step49,
      word39Step50, word39Step51, word39Step52, word39Step53, word39Step54,
      word39Step55, word39Step56, word39Step57]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
