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
private def word9Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word9State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word9Step0 :
    word9Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word9State1 := by decide +kernel

private def word9Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .s, .h]
private def word9State2 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(1 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(1 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word9Step1 :
    word9Chunk1.foldl (fun acc a => a.applyPacked acc)
      word9State1 = word9State2 := by decide +kernel

private def word9Chunk2 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word9State3 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word9Step2 :
    word9Chunk2.foldl (fun acc a => a.applyPacked acc)
      word9State2 = word9State3 := by decide +kernel

private def word9Chunk3 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word9State4 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word9Step3 :
    word9Chunk3.foldl (fun acc a => a.applyPacked acc)
      word9State3 = word9State4 := by decide +kernel

private def word9Chunk4 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word9State5 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word9Step4 :
    word9Chunk4.foldl (fun acc a => a.applyPacked acc)
      word9State4 = word9State5 := by decide +kernel

private def word9Chunk5 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word9State6 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word9Step5 :
    word9Chunk5.foldl (fun acc a => a.applyPacked acc)
      word9State5 = word9State6 := by decide +kernel

private def word9Chunk6 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word9State7 : PackedMat2 :=
    ⟨⟨⟨((7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word9Step6 :
    word9Chunk6.foldl (fun acc a => a.applyPacked acc)
      word9State6 = word9State7 := by decide +kernel

private def word9Chunk7 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word9State8 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((25 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((9 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word9Step7 :
    word9Chunk7.foldl (fun acc a => a.applyPacked acc)
      word9State7 = word9State8 := by decide +kernel

private def word9Chunk8 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word9State9 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((31 : Dyadic) * half ^ 6),
        ((17 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 6),
        ((-5 : Dyadic) * half ^ 4)⟩,
       ⟨((-35 : Dyadic) * half ^ 6),
        ((15 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 6),
        ((-17 : Dyadic) * half ^ 6)⟩,
       ⟨((-35 : Dyadic) * half ^ 6),
        ((9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-23 : Dyadic) * half ^ 6),
        ((-17 : Dyadic) * half ^ 6)⟩,
       ⟨((11 : Dyadic) * half ^ 6),
        ((7 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word9Step8 :
    word9Chunk8.foldl (fun acc a => a.applyPacked acc)
      word9State8 = word9State9 := by decide +kernel

private def word9Chunk9 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word9State10 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((-29 : Dyadic) * half ^ 7)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((57 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 7)⟩,
       ⟨((17 : Dyadic) * half ^ 6),
        ((-49 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 6),
        ((-3 : Dyadic) * half ^ 7)⟩,
       ⟨((17 : Dyadic) * half ^ 6),
        ((-49 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-29 : Dyadic) * half ^ 7)⟩,
       ⟨((-9 : Dyadic) * half ^ 5),
        ((-57 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word9Step9 :
    word9Chunk9.foldl (fun acc a => a.applyPacked acc)
      word9State9 = word9State10 := by decide +kernel

private def word9Chunk10 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word9State11 : PackedMat2 :=
    ⟨⟨⟨((-41 : Dyadic) * half ^ 6),
        ((-41 : Dyadic) * half ^ 8)⟩,
       ⟨((21 : Dyadic) * half ^ 7),
        ((-109 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((13 : Dyadic) * half ^ 8)⟩,
       ⟨((-45 : Dyadic) * half ^ 7),
        ((25 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 6),
        ((49 : Dyadic) * half ^ 8)⟩,
       ⟨((-19 : Dyadic) * half ^ 7),
        ((41 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 6),
        ((103 : Dyadic) * half ^ 8)⟩,
       ⟨((-75 : Dyadic) * half ^ 7),
        ((-61 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word9Step10 :
    word9Chunk10.foldl (fun acc a => a.applyPacked acc)
      word9State10 = word9State11 := by decide +kernel

private def word9Chunk11 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word9State12 : PackedMat2 :=
    ⟨⟨⟨((-29 : Dyadic) * half ^ 7),
        ((-21 : Dyadic) * half ^ 8)⟩,
       ⟨((-73 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((35 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 6)⟩,
       ⟨((25 : Dyadic) * half ^ 7),
        ((-93 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-81 : Dyadic) * half ^ 8),
        ((95 : Dyadic) * half ^ 8)⟩,
       ⟨((105 : Dyadic) * half ^ 8),
        ((45 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((33 : Dyadic) * half ^ 8),
        ((51 : Dyadic) * half ^ 7)⟩,
       ⟨((9 : Dyadic) * half ^ 8),
        ((-11 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word9Step11 :
    word9Chunk11.foldl (fun acc a => a.applyPacked acc)
      word9State11 = word9State12 := by decide +kernel

private def word9Chunk12 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word9State13 : PackedMat2 :=
    ⟨⟨⟨((23 : Dyadic) * half ^ 9),
        ((49 : Dyadic) * half ^ 9)⟩,
       ⟨((23 : Dyadic) * half ^ 9),
        ((-61 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 9),
        ((335 : Dyadic) * half ^ 9)⟩,
       ⟨((-37 : Dyadic) * half ^ 9),
        ((9 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 9),
        ((-335 : Dyadic) * half ^ 9)⟩,
       ⟨((-37 : Dyadic) * half ^ 9),
        ((9 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((23 : Dyadic) * half ^ 9),
        ((49 : Dyadic) * half ^ 9)⟩,
       ⟨((-23 : Dyadic) * half ^ 9),
        ((61 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word9Step12 :
    word9Chunk12.foldl (fun acc a => a.applyPacked acc)
      word9State12 = word9State13 := by decide +kernel

private def word9Chunk13 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word9State14 : PackedMat2 :=
    ⟨⟨⟨((-41 : Dyadic) * half ^ 10),
        ((-105 : Dyadic) * half ^ 9)⟩,
       ⟨((-21 : Dyadic) * half ^ 10),
        ((107 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((333 : Dyadic) * half ^ 10),
        ((157 : Dyadic) * half ^ 9)⟩,
       ⟨((765 : Dyadic) * half ^ 10),
        ((-145 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((333 : Dyadic) * half ^ 10),
        ((157 : Dyadic) * half ^ 9)⟩,
       ⟨((-765 : Dyadic) * half ^ 10),
        ((145 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((41 : Dyadic) * half ^ 10),
        ((105 : Dyadic) * half ^ 9)⟩,
       ⟨((-21 : Dyadic) * half ^ 10),
        ((107 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word9Step13 :
    word9Chunk13.foldl (fun acc a => a.applyPacked acc)
      word9State13 = word9State14 := by decide +kernel

private def word9Chunk14 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word9State15 : PackedMat2 :=
    ⟨⟨⟨((-519 : Dyadic) * half ^ 11),
        ((127 : Dyadic) * half ^ 10)⟩,
       ⟨((-497 : Dyadic) * half ^ 11),
        ((117 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((165 : Dyadic) * half ^ 11),
        ((165 : Dyadic) * half ^ 10)⟩,
       ⟨((1807 : Dyadic) * half ^ 11),
        ((75 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-405 : Dyadic) * half ^ 11),
        ((-493 : Dyadic) * half ^ 10)⟩,
       ⟨((-255 : Dyadic) * half ^ 11),
        ((821 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((371 : Dyadic) * half ^ 11),
        ((-127 : Dyadic) * half ^ 9)⟩,
       ⟨((137 : Dyadic) * half ^ 11),
        ((-11 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word9Step14 :
    word9Chunk14.foldl (fun acc a => a.applyPacked acc)
      word9State14 = word9State15 := by decide +kernel

private def word9Chunk15 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word9State16 : PackedMat2 :=
    ⟨⟨⟨((-401 : Dyadic) * half ^ 11),
        ((-711 : Dyadic) * half ^ 12)⟩,
       ⟨((-225 : Dyadic) * half ^ 11),
        ((-573 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-411 : Dyadic) * half ^ 10),
        ((207 : Dyadic) * half ^ 12)⟩,
       ⟨((-51 : Dyadic) * half ^ 10),
        ((2391 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-411 : Dyadic) * half ^ 10),
        ((207 : Dyadic) * half ^ 12)⟩,
       ⟨((51 : Dyadic) * half ^ 10),
        ((-2391 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((401 : Dyadic) * half ^ 11),
        ((711 : Dyadic) * half ^ 12)⟩,
       ⟨((-225 : Dyadic) * half ^ 11),
        ((-573 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word9Step15 :
    word9Chunk15.foldl (fun acc a => a.applyPacked acc)
      word9State15 = word9State16 := by decide +kernel

private def word9Chunk16 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word9State17 : PackedMat2 :=
    ⟨⟨⟨((-227 : Dyadic) * half ^ 11),
        ((-29 : Dyadic) * half ^ 11)⟩,
       ⟨((-2465 : Dyadic) * half ^ 12),
        ((-487 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-2081 : Dyadic) * half ^ 12),
        ((431 : Dyadic) * half ^ 11)⟩,
       ⟨((391 : Dyadic) * half ^ 10),
        ((-405 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((2081 : Dyadic) * half ^ 12),
        ((-431 : Dyadic) * half ^ 11)⟩,
       ⟨((391 : Dyadic) * half ^ 10),
        ((-405 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-227 : Dyadic) * half ^ 11),
        ((-29 : Dyadic) * half ^ 11)⟩,
       ⟨((2465 : Dyadic) * half ^ 12),
        ((487 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word9Step16 :
    word9Chunk16.foldl (fun acc a => a.applyPacked acc)
      word9State16 = word9State17 := by decide +kernel

private def word9Chunk17 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word9State18 : PackedMat2 :=
    ⟨⟨⟨((541 : Dyadic) * half ^ 12),
        ((4685 : Dyadic) * half ^ 14)⟩,
       ⟨((-1945 : Dyadic) * half ^ 13),
        ((-5563 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((269 : Dyadic) * half ^ 11),
        ((-1341 : Dyadic) * half ^ 14)⟩,
       ⟨((-1859 : Dyadic) * half ^ 13),
        ((7771 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1139 : Dyadic) * half ^ 11),
        ((2935 : Dyadic) * half ^ 14)⟩,
       ⟨((-3215 : Dyadic) * half ^ 13),
        ((783 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1281 : Dyadic) * half ^ 11),
        ((-3027 : Dyadic) * half ^ 14)⟩,
       ⟨((-439 : Dyadic) * half ^ 13),
        ((-863 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word9Step17 :
    word9Chunk17.foldl (fun acc a => a.applyPacked acc)
      word9State17 = word9State18 := by decide +kernel

private def word9Chunk18 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word9State19 : PackedMat2 :=
    ⟨⟨⟨((2777 : Dyadic) * half ^ 13),
        ((2267 : Dyadic) * half ^ 13)⟩,
       ⟨((-1585 : Dyadic) * half ^ 12),
        ((4283 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((25 : Dyadic) * half ^ 8),
        ((-467 : Dyadic) * half ^ 14)⟩,
       ⟨((1349 : Dyadic) * half ^ 11),
        ((63 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-215 : Dyadic) * half ^ 14),
        ((1549 : Dyadic) * half ^ 12)⟩,
       ⟨((-719 : Dyadic) * half ^ 14),
        ((-1149 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-8817 : Dyadic) * half ^ 14),
        ((393 : Dyadic) * half ^ 14)⟩,
       ⟨((-251 : Dyadic) * half ^ 14),
        ((-5947 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word9Step18 :
    word9Chunk18.foldl (fun acc a => a.applyPacked acc)
      word9State18 = word9State19 := by decide +kernel

private def word9Chunk19 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word9State20 : PackedMat2 :=
    ⟨⟨⟨((11347 : Dyadic) * half ^ 15),
        ((8989 : Dyadic) * half ^ 15)⟩,
       ⟨((3745 : Dyadic) * half ^ 15),
        ((5965 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-1835 : Dyadic) * half ^ 15),
        ((-4437 : Dyadic) * half ^ 14)⟩,
       ⟨((21197 : Dyadic) * half ^ 15),
        ((-3317 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-21197 : Dyadic) * half ^ 15),
        ((3317 : Dyadic) * half ^ 14)⟩,
       ⟨((1835 : Dyadic) * half ^ 15),
        ((4437 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((3745 : Dyadic) * half ^ 15),
        ((5965 : Dyadic) * half ^ 15)⟩,
       ⟨((11347 : Dyadic) * half ^ 15),
        ((8989 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word9Step19 :
    word9Chunk19.foldl (fun acc a => a.applyPacked acc)
      word9State19 = word9State20 := by decide +kernel

private def word9Chunk20 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word9State21 : PackedMat2 :=
    ⟨⟨⟨((16473 : Dyadic) * half ^ 16),
        ((8449 : Dyadic) * half ^ 15)⟩,
       ⟨((7769 : Dyadic) * half ^ 16),
        ((22415 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-35921 : Dyadic) * half ^ 16),
        ((1075 : Dyadic) * half ^ 13)⟩,
       ⟨((-30057 : Dyadic) * half ^ 16),
        ((4777 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-35921 : Dyadic) * half ^ 16),
        ((1075 : Dyadic) * half ^ 13)⟩,
       ⟨((30057 : Dyadic) * half ^ 16),
        ((-4777 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-16473 : Dyadic) * half ^ 16),
        ((-8449 : Dyadic) * half ^ 15)⟩,
       ⟨((7769 : Dyadic) * half ^ 16),
        ((22415 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word9Step20 :
    word9Chunk20.foldl (fun acc a => a.applyPacked acc)
      word9State20 = word9State21 := by decide +kernel

private def word9Chunk21 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word9State22 : PackedMat2 :=
    ⟨⟨⟨((15487 : Dyadic) * half ^ 15),
        ((-7271 : Dyadic) * half ^ 16)⟩,
       ⟨((15623 : Dyadic) * half ^ 16),
        ((7361 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((31865 : Dyadic) * half ^ 16),
        ((-2975 : Dyadic) * half ^ 14)⟩,
       ⟨((-4267 : Dyadic) * half ^ 14),
        ((-1371 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-2509 : Dyadic) * half ^ 14),
        ((-48933 : Dyadic) * half ^ 17)⟩,
       ⟨((-8459 : Dyadic) * half ^ 14),
        ((14797 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-21993 : Dyadic) * half ^ 16),
        ((15351 : Dyadic) * half ^ 17)⟩,
       ⟨((-7451 : Dyadic) * half ^ 16),
        ((-46597 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word9Step21 :
    word9Chunk21.foldl (fun acc a => a.applyPacked acc)
      word9State21 = word9State22 := by decide +kernel

private def word9Chunk22 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word9State23 : PackedMat2 :=
    ⟨⟨⟨((1521 : Dyadic) * half ^ 16),
        ((-27567 : Dyadic) * half ^ 17)⟩,
       ⟨((-95185 : Dyadic) * half ^ 17),
        ((10165 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((23369 : Dyadic) * half ^ 17),
        ((2313 : Dyadic) * half ^ 14)⟩,
       ⟨((-3179 : Dyadic) * half ^ 13),
        ((-3899 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((23369 : Dyadic) * half ^ 17),
        ((2313 : Dyadic) * half ^ 14)⟩,
       ⟨((3179 : Dyadic) * half ^ 13),
        ((3899 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1521 : Dyadic) * half ^ 16),
        ((27567 : Dyadic) * half ^ 17)⟩,
       ⟨((-95185 : Dyadic) * half ^ 17),
        ((10165 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word9Step22 :
    word9Chunk22.foldl (fun acc a => a.applyPacked acc)
      word9State22 = word9State23 := by decide +kernel

private def word9Chunk23 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word9State24 : PackedMat2 :=
    ⟨⟨⟨((67615 : Dyadic) * half ^ 18),
        ((149709 : Dyadic) * half ^ 19)⟩,
       ⟨((70927 : Dyadic) * half ^ 17),
        ((-125553 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((74149 : Dyadic) * half ^ 18),
        ((154743 : Dyadic) * half ^ 19)⟩,
       ⟨((-4205 : Dyadic) * half ^ 15),
        ((112557 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-21093 : Dyadic) * half ^ 18),
        ((-107789 : Dyadic) * half ^ 19)⟩,
       ⟨((66825 : Dyadic) * half ^ 17),
        ((40509 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((137631 : Dyadic) * half ^ 18),
        ((-74239 : Dyadic) * half ^ 19)⟩,
       ⟨((-6039 : Dyadic) * half ^ 17),
        ((-209469 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word9Step23 :
    word9Chunk23.foldl (fun acc a => a.applyPacked acc)
      word9State23 = word9State24 := by decide +kernel

private def word9Chunk24 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word9State25 : PackedMat2 :=
    ⟨⟨⟨((-10267 : Dyadic) * half ^ 17),
        ((74065 : Dyadic) * half ^ 17)⟩,
       ⟨((-15453 : Dyadic) * half ^ 17),
        ((28943 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((811 : Dyadic) * half ^ 12),
        ((78467 : Dyadic) * half ^ 19)⟩,
       ⟨((15747 : Dyadic) * half ^ 18),
        ((92245 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-262957 : Dyadic) * half ^ 19),
        ((-67651 : Dyadic) * half ^ 19)⟩,
       ⟨((106023 : Dyadic) * half ^ 19),
        ((-36157 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((325203 : Dyadic) * half ^ 19),
        ((-3215 : Dyadic) * half ^ 15)⟩,
       ⟨((267317 : Dyadic) * half ^ 19),
        ((2593 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word9Step24 :
    word9Chunk24.foldl (fun acc a => a.applyPacked acc)
      word9State24 = word9State25 := by decide +kernel

private def word9Chunk25 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word9State26 : PackedMat2 :=
    ⟨⟨⟨((-257995 : Dyadic) * half ^ 20),
        ((-174365 : Dyadic) * half ^ 20)⟩,
       ⟨((330413 : Dyadic) * half ^ 20),
        ((-163901 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((66169 : Dyadic) * half ^ 20),
        ((143371 : Dyadic) * half ^ 19)⟩,
       ⟨((-17329 : Dyadic) * half ^ 20),
        ((141435 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-17329 : Dyadic) * half ^ 20),
        ((141435 : Dyadic) * half ^ 18)⟩,
       ⟨((66169 : Dyadic) * half ^ 20),
        ((143371 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-330413 : Dyadic) * half ^ 20),
        ((163901 : Dyadic) * half ^ 20)⟩,
       ⟨((257995 : Dyadic) * half ^ 20),
        ((174365 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word9Step25 :
    word9Chunk25.foldl (fun acc a => a.applyPacked acc)
      word9State25 = word9State26 := by decide +kernel

private def word9Chunk26 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word9State27 : PackedMat2 :=
    ⟨⟨⟨((-1531625 : Dyadic) * half ^ 21),
        ((-59257 : Dyadic) * half ^ 20)⟩,
       ⟨((-306799 : Dyadic) * half ^ 21),
        ((114299 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((252547 : Dyadic) * half ^ 21),
        ((-231681 : Dyadic) * half ^ 20)⟩,
       ⟨((1187185 : Dyadic) * half ^ 21),
        ((-24791 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((488153 : Dyadic) * half ^ 21),
        ((-359933 : Dyadic) * half ^ 20)⟩,
       ⟨((438571 : Dyadic) * half ^ 21),
        ((467319 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-4215 : Dyadic) * half ^ 21),
        ((-229803 : Dyadic) * half ^ 19)⟩,
       ⟨((-232813 : Dyadic) * half ^ 21),
        ((-612413 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word9Step26 :
    word9Chunk26.foldl (fun acc a => a.applyPacked acc)
      word9State26 = word9State27 := by decide +kernel

private def word9Chunk27 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word9State28 : PackedMat2 :=
    ⟨⟨⟨((-22847 : Dyadic) * half ^ 19),
        ((-591281 : Dyadic) * half ^ 21)⟩,
       ⟨((-57921 : Dyadic) * half ^ 21),
        ((-56263 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-1822767 : Dyadic) * half ^ 21),
        ((19853 : Dyadic) * half ^ 19)⟩,
       ⟨((127441 : Dyadic) * half ^ 20),
        ((152381 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-1822767 : Dyadic) * half ^ 21),
        ((19853 : Dyadic) * half ^ 19)⟩,
       ⟨((-127441 : Dyadic) * half ^ 20),
        ((-152381 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((22847 : Dyadic) * half ^ 19),
        ((591281 : Dyadic) * half ^ 21)⟩,
       ⟨((-57921 : Dyadic) * half ^ 21),
        ((-56263 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word9Step27 :
    word9Chunk27.foldl (fun acc a => a.applyPacked acc)
      word9State27 = word9State28 := by decide +kernel

private def word9Chunk28 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word9State29 : PackedMat2 :=
    ⟨⟨⟨((1205177 : Dyadic) * half ^ 22),
        ((51685 : Dyadic) * half ^ 18)⟩,
       ⟨((-1862743 : Dyadic) * half ^ 22),
        ((-236579 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-2515249 : Dyadic) * half ^ 22),
        ((1071673 : Dyadic) * half ^ 22)⟩,
       ⟨((937253 : Dyadic) * half ^ 22),
        ((-68127 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((501773 : Dyadic) * half ^ 21),
        ((-394499 : Dyadic) * half ^ 21)⟩,
       ⟨((142475 : Dyadic) * half ^ 19),
        ((-1726251 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((29839 : Dyadic) * half ^ 20),
        ((328783 : Dyadic) * half ^ 22)⟩,
       ⟨((-443319 : Dyadic) * half ^ 20),
        ((-191745 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word9Step28 :
    word9Chunk28.foldl (fun acc a => a.applyPacked acc)
      word9State28 = word9State29 := by decide +kernel

private def word9Chunk29 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word9State30 : PackedMat2 :=
    ⟨⟨⟨((-84407 : Dyadic) * half ^ 23),
        ((2724989 : Dyadic) * half ^ 23)⟩,
       ⟨((2011311 : Dyadic) * half ^ 23),
        ((378155 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((1512619 : Dyadic) * half ^ 23),
        ((-3556757 : Dyadic) * half ^ 23)⟩,
       ⟨((-4311699 : Dyadic) * half ^ 23),
        ((-297757 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-1512619 : Dyadic) * half ^ 23),
        ((3556757 : Dyadic) * half ^ 23)⟩,
       ⟨((-4311699 : Dyadic) * half ^ 23),
        ((-297757 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-84407 : Dyadic) * half ^ 23),
        ((2724989 : Dyadic) * half ^ 23)⟩,
       ⟨((-2011311 : Dyadic) * half ^ 23),
        ((-378155 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word9Step29 :
    word9Chunk29.foldl (fun acc a => a.applyPacked acc)
      word9State29 = word9State30 := by decide +kernel

private def word9Chunk30 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word9State31 : PackedMat2 :=
    ⟨⟨⟨((1307799 : Dyadic) * half ^ 24),
        ((394801 : Dyadic) * half ^ 23)⟩,
       ⟨((6015403 : Dyadic) * half ^ 24),
        ((-3916921 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-2088139 : Dyadic) * half ^ 24),
        ((1777927 : Dyadic) * half ^ 23)⟩,
       ⟨((-13097259 : Dyadic) * half ^ 24),
        ((-2287069 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((1268785 : Dyadic) * half ^ 24),
        ((-7592699 : Dyadic) * half ^ 24)⟩,
       ⟨((5842923 : Dyadic) * half ^ 24),
        ((344035 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((3127319 : Dyadic) * half ^ 24),
        ((-3661601 : Dyadic) * half ^ 24)⟩,
       ⟨((-4706523 : Dyadic) * half ^ 24),
        ((1176901 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word9Step30 :
    word9Chunk30.foldl (fun acc a => a.applyPacked acc)
      word9State30 = word9State31 := by decide +kernel

private def word9Chunk31 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word9State32 : PackedMat2 :=
    ⟨⟨⟨((2165265 : Dyadic) * half ^ 23),
        ((7511789 : Dyadic) * half ^ 25)⟩,
       ⟨((-277369 : Dyadic) * half ^ 21),
        ((3249151 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((13112185 : Dyadic) * half ^ 24),
        ((-3717991 : Dyadic) * half ^ 25)⟩,
       ⟨((-2677239 : Dyadic) * half ^ 24),
        ((-8751803 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-13112185 : Dyadic) * half ^ 24),
        ((3717991 : Dyadic) * half ^ 25)⟩,
       ⟨((-2677239 : Dyadic) * half ^ 24),
        ((-8751803 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((2165265 : Dyadic) * half ^ 23),
        ((7511789 : Dyadic) * half ^ 25)⟩,
       ⟨((277369 : Dyadic) * half ^ 21),
        ((-3249151 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word9Step31 :
    word9Chunk31.foldl (fun acc a => a.applyPacked acc)
      word9State31 = word9State32 := by decide +kernel

private def word9Chunk32 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word9State33 : PackedMat2 :=
    ⟨⟨⟨((7982819 : Dyadic) * half ^ 24),
        ((-5023037 : Dyadic) * half ^ 26)⟩,
       ⟨((5062775 : Dyadic) * half ^ 25),
        ((-12715539 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((2169859 : Dyadic) * half ^ 24),
        ((37087751 : Dyadic) * half ^ 26)⟩,
       ⟨((6491701 : Dyadic) * half ^ 25),
        ((-2522987 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((19805369 : Dyadic) * half ^ 25),
        ((-2151983 : Dyadic) * half ^ 26)⟩,
       ⟨((-8641191 : Dyadic) * half ^ 24),
        ((-10831419 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-3846251 : Dyadic) * half ^ 25),
        ((-10902863 : Dyadic) * half ^ 26)⟩,
       ⟨((-1108661 : Dyadic) * half ^ 22),
        ((21028413 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word9Step32 :
    word9Chunk32.foldl (fun acc a => a.applyPacked acc)
      word9State32 = word9State33 := by decide +kernel

private def word9Chunk33 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word9State34 : PackedMat2 :=
    ⟨⟨⟨((-2873047 : Dyadic) * half ^ 25),
        ((40867283 : Dyadic) * half ^ 26)⟩,
       ⟨((-1620801 : Dyadic) * half ^ 25),
        ((1906375 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((3657603 : Dyadic) * half ^ 24),
        ((4056365 : Dyadic) * half ^ 25)⟩,
       ⟨((3439753 : Dyadic) * half ^ 25),
        ((18677807 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((3439753 : Dyadic) * half ^ 25),
        ((18677807 : Dyadic) * half ^ 26)⟩,
       ⟨((3657603 : Dyadic) * half ^ 24),
        ((4056365 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((1620801 : Dyadic) * half ^ 25),
        ((-1906375 : Dyadic) * half ^ 25)⟩,
       ⟨((2873047 : Dyadic) * half ^ 25),
        ((-40867283 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word9Step33 :
    word9Chunk33.foldl (fun acc a => a.applyPacked acc)
      word9State33 = word9State34 := by decide +kernel

private def word9Chunk34 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word9State35 : PackedMat2 :=
    ⟨⟨⟨((43550289 : Dyadic) * half ^ 27),
        ((31430863 : Dyadic) * half ^ 27)⟩,
       ⟨((105667251 : Dyadic) * half ^ 27),
        ((-5183687 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-23552921 : Dyadic) * half ^ 27),
        ((8494759 : Dyadic) * half ^ 25)⟩,
       ⟨((-5345621 : Dyadic) * half ^ 27),
        ((1942867 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((5345621 : Dyadic) * half ^ 27),
        ((-1942867 : Dyadic) * half ^ 26)⟩,
       ⟨((23552921 : Dyadic) * half ^ 27),
        ((-8494759 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((105667251 : Dyadic) * half ^ 27),
        ((-5183687 : Dyadic) * half ^ 27)⟩,
       ⟨((43550289 : Dyadic) * half ^ 27),
        ((31430863 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word9Step34 :
    word9Chunk34.foldl (fun acc a => a.applyPacked acc)
      word9State34 = word9State35 := by decide +kernel

private def word9Chunk35 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word9State36 : PackedMat2 :=
    ⟨⟨⟨((-80670295 : Dyadic) * half ^ 28),
        ((63183247 : Dyadic) * half ^ 28)⟩,
       ⟨((3089613 : Dyadic) * half ^ 28),
        ((36550441 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((99550869 : Dyadic) * half ^ 28),
        ((47170115 : Dyadic) * half ^ 28)⟩,
       ⟨((20833097 : Dyadic) * half ^ 28),
        ((-1212533 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((44745049 : Dyadic) * half ^ 28),
        ((60191983 : Dyadic) * half ^ 28)⟩,
       ⟨((49595181 : Dyadic) * half ^ 28),
        ((19679443 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-209385011 : Dyadic) * half ^ 28),
        ((38790341 : Dyadic) * half ^ 28)⟩,
       ⟨((83018517 : Dyadic) * half ^ 28),
        ((20939977 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word9Step35 :
    word9Chunk35.foldl (fun acc a => a.applyPacked acc)
      word9State35 = word9State36 := by decide +kernel

private def word9Chunk36 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word9State37 : PackedMat2 :=
    ⟨⟨⟨((-210243705 : Dyadic) * half ^ 29),
        ((47028409 : Dyadic) * half ^ 28)⟩,
       ⟨((400977213 : Dyadic) * half ^ 29),
        ((36956795 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((4800807 : Dyadic) * half ^ 29),
        ((-27461225 : Dyadic) * half ^ 28)⟩,
       ⟨((31252985 : Dyadic) * half ^ 29),
        ((167014233 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-112091783 : Dyadic) * half ^ 29),
        ((-1126681 : Dyadic) * half ^ 25)⟩,
       ⟨((221936683 : Dyadic) * half ^ 29),
        ((13226089 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((131013613 : Dyadic) * half ^ 29),
        ((47683377 : Dyadic) * half ^ 28)⟩,
       ⟨((57100023 : Dyadic) * half ^ 29),
        ((-305610459 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word9Step36 :
    word9Chunk36.foldl (fun acc a => a.applyPacked acc)
      word9State36 = word9State37 := by decide +kernel

private def word9Chunk37 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word9State38 : PackedMat2 :=
    ⟨⟨⟨((-1700503 : Dyadic) * half ^ 23),
        ((-96139025 : Dyadic) * half ^ 29)⟩,
       ⟨((-52538565 : Dyadic) * half ^ 29),
        ((82756033 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-175670795 : Dyadic) * half ^ 29),
        ((-1064947 : Dyadic) * half ^ 24)⟩,
       ⟨((-15536985 : Dyadic) * half ^ 28),
        ((-15156565 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-175670795 : Dyadic) * half ^ 29),
        ((-1064947 : Dyadic) * half ^ 24)⟩,
       ⟨((15536985 : Dyadic) * half ^ 28),
        ((15156565 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((1700503 : Dyadic) * half ^ 23),
        ((96139025 : Dyadic) * half ^ 29)⟩,
       ⟨((-52538565 : Dyadic) * half ^ 29),
        ((82756033 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word9Step37 :
    word9Chunk37.foldl (fun acc a => a.applyPacked acc)
      word9State37 = word9State38 := by decide +kernel

private def word9Chunk38 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word9State39 : PackedMat2 :=
    ⟨⟨⟨((-143504659 : Dyadic) * half ^ 30),
        ((-1024309473 : Dyadic) * half ^ 31)⟩,
       ⟨((308803753 : Dyadic) * half ^ 29),
        ((-90610415 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((390080519 : Dyadic) * half ^ 30),
        ((-234421703 : Dyadic) * half ^ 31)⟩,
       ⟨((-352987 : Dyadic) * half ^ 28),
        ((-291675305 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-28626801 : Dyadic) * half ^ 30),
        ((-391492467 : Dyadic) * half ^ 31)⟩,
       ⟨((-32881063 : Dyadic) * half ^ 27),
        ((388668571 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-466849529 : Dyadic) * half ^ 30),
        ((-761112165 : Dyadic) * half ^ 31)⟩,
       ⟨((69682493 : Dyadic) * half ^ 27),
        ((-474102847 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word9Step38 :
    word9Chunk38.foldl (fun acc a => a.applyPacked acc)
      word9State38 = word9State39 := by decide +kernel

private def word9Chunk39 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word9State40 : PackedMat2 :=
    ⟨⟨⟨((-1643328927 : Dyadic) * half ^ 31),
        ((-15252319 : Dyadic) * half ^ 27)⟩,
       ⟨((155965445 : Dyadic) * half ^ 31),
        ((-5879041 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-850617261 : Dyadic) * half ^ 31),
        ((581223379 : Dyadic) * half ^ 31)⟩,
       ⟨((241909873 : Dyadic) * half ^ 31),
        ((393531937 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-241909873 : Dyadic) * half ^ 31),
        ((-393531937 : Dyadic) * half ^ 31)⟩,
       ⟨((850617261 : Dyadic) * half ^ 31),
        ((-581223379 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((155965445 : Dyadic) * half ^ 31),
        ((-5879041 : Dyadic) * half ^ 30)⟩,
       ⟨((-1643328927 : Dyadic) * half ^ 31),
        ((-15252319 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word9Step39 :
    word9Chunk39.foldl (fun acc a => a.applyPacked acc)
      word9State39 = word9State40 := by decide +kernel

private def word9Chunk40 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word9State41 : PackedMat2 :=
    ⟨⟨⟨((330715663 : Dyadic) * half ^ 32),
        ((-1935924539 : Dyadic) * half ^ 32)⟩,
       ⟨((-1479153649 : Dyadic) * half ^ 32),
        ((-317167613 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((1176332071 : Dyadic) * half ^ 32),
        ((-500467457 : Dyadic) * half ^ 32)⟩,
       ⟨((168725635 : Dyadic) * half ^ 32),
        ((861390219 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((1222312981 : Dyadic) * half ^ 32),
        ((672528853 : Dyadic) * half ^ 32)⟩,
       ⟨((-2223247895 : Dyadic) * half ^ 32),
        ((251901609 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((2570259765 : Dyadic) * half ^ 32),
        ((574218993 : Dyadic) * half ^ 32)⟩,
       ⟨((1301589313 : Dyadic) * half ^ 32),
        ((-3534901 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word9Step40 :
    word9Chunk40.foldl (fun acc a => a.applyPacked acc)
      word9State40 = word9State41 := by decide +kernel

private def word9Chunk41 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word9State42 : PackedMat2 :=
    ⟨⟨⟨((986972813 : Dyadic) * half ^ 31),
        ((-1365041307 : Dyadic) * half ^ 33)⟩,
       ⟨((-694852173 : Dyadic) * half ^ 32),
        ((2665908721 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-31776705 : Dyadic) * half ^ 28),
        ((-2203986193 : Dyadic) * half ^ 33)⟩,
       ⟨((997445577 : Dyadic) * half ^ 32),
        ((3435137875 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((997445577 : Dyadic) * half ^ 32),
        ((3435137875 : Dyadic) * half ^ 33)⟩,
       ⟨((-31776705 : Dyadic) * half ^ 28),
        ((-2203986193 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((694852173 : Dyadic) * half ^ 32),
        ((-2665908721 : Dyadic) * half ^ 33)⟩,
       ⟨((-986972813 : Dyadic) * half ^ 31),
        ((1365041307 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word9Step41 :
    word9Chunk41.foldl (fun acc a => a.applyPacked acc)
      word9State41 = word9State42 := by decide +kernel

private def word9Chunk42 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word9State43 : PackedMat2 :=
    ⟨⟨⟨((-373402281 : Dyadic) * half ^ 32),
        ((5627105097 : Dyadic) * half ^ 34)⟩,
       ⟨((-3221415371 : Dyadic) * half ^ 33),
        ((1940524779 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-3132561455 : Dyadic) * half ^ 32),
        ((-1843324127 : Dyadic) * half ^ 34)⟩,
       ⟨((-385359073 : Dyadic) * half ^ 33),
        ((2841682439 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((385359073 : Dyadic) * half ^ 33),
        ((-2841682439 : Dyadic) * half ^ 34)⟩,
       ⟨((3132561455 : Dyadic) * half ^ 32),
        ((1843324127 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-3221415371 : Dyadic) * half ^ 33),
        ((1940524779 : Dyadic) * half ^ 34)⟩,
       ⟨((-373402281 : Dyadic) * half ^ 32),
        ((5627105097 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word9Step42 :
    word9Chunk42.foldl (fun acc a => a.applyPacked acc)
      word9State42 = word9State43 := by decide +kernel

private def word9Chunk43 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word9State44 : PackedMat2 :=
    ⟨⟨⟨((664041367 : Dyadic) * half ^ 31),
        ((389365729 : Dyadic) * half ^ 33)⟩,
       ⟨((4300464515 : Dyadic) * half ^ 33),
        ((2799062111 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((4045896819 : Dyadic) * half ^ 33),
        ((-5423171041 : Dyadic) * half ^ 34)⟩,
       ⟨((-1768647261 : Dyadic) * half ^ 33),
        ((-2215219435 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-1768647261 : Dyadic) * half ^ 33),
        ((-2215219435 : Dyadic) * half ^ 33)⟩,
       ⟨((4045896819 : Dyadic) * half ^ 33),
        ((-5423171041 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-4300464515 : Dyadic) * half ^ 33),
        ((-2799062111 : Dyadic) * half ^ 34)⟩,
       ⟨((-664041367 : Dyadic) * half ^ 31),
        ((-389365729 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word9Step43 :
    word9Chunk43.foldl (fun acc a => a.applyPacked acc)
      word9State43 = word9State44 := by decide +kernel

private def word9Chunk44 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word9State45 : PackedMat2 :=
    ⟨⟨⟨((-7802598163 : Dyadic) * half ^ 35),
        ((10359470371 : Dyadic) * half ^ 35)⟩,
       ⟨((12396296097 : Dyadic) * half ^ 35),
        ((395826873 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((7087809185 : Dyadic) * half ^ 35),
        ((2063248845 : Dyadic) * half ^ 35)⟩,
       ⟨((-3053697743 : Dyadic) * half ^ 35),
        ((-9233608051 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-7087809185 : Dyadic) * half ^ 35),
        ((-2063248845 : Dyadic) * half ^ 35)⟩,
       ⟨((-3053697743 : Dyadic) * half ^ 35),
        ((-9233608051 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-7802598163 : Dyadic) * half ^ 35),
        ((10359470371 : Dyadic) * half ^ 35)⟩,
       ⟨((-12396296097 : Dyadic) * half ^ 35),
        ((-395826873 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word9Step44 :
    word9Chunk44.foldl (fun acc a => a.applyPacked acc)
      word9State44 = word9State45 := by decide +kernel

private def word9Chunk45 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word9State46 : PackedMat2 :=
    ⟨⟨⟨((308708865 : Dyadic) * half ^ 34),
        ((-5328750377 : Dyadic) * half ^ 35)⟩,
       ⟨((-4636494207 : Dyadic) * half ^ 35),
        ((2144275183 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-311201365 : Dyadic) * half ^ 35),
        ((17957247829 : Dyadic) * half ^ 35)⟩,
       ⟨((-10560729779 : Dyadic) * half ^ 34),
        ((-445525661 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((18848299151 : Dyadic) * half ^ 35),
        ((20810258193 : Dyadic) * half ^ 36)⟩,
       ⟨((-17066196507 : Dyadic) * half ^ 35),
        ((21432660923 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((934128195 : Dyadic) * half ^ 32),
        ((-5253911937 : Dyadic) * half ^ 36)⟩,
       ⟨((-1592237597 : Dyadic) * half ^ 34),
        ((-4019076477 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word9Step45 :
    word9Chunk45.foldl (fun acc a => a.applyPacked acc)
      word9State45 = word9State46 := by decide +kernel

private def word9Chunk46 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word9State47 : PackedMat2 :=
    ⟨⟨⟨((21935403097 : Dyadic) * half ^ 36),
        ((9754318087 : Dyadic) * half ^ 35)⟩,
       ⟨((-6862861217 : Dyadic) * half ^ 35),
        ((34746431461 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((1246508759 : Dyadic) * half ^ 34),
        ((4437600199 : Dyadic) * half ^ 34)⟩,
       ⟨((3884962753 : Dyadic) * half ^ 36),
        ((-2542755705 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1246508759 : Dyadic) * half ^ 34),
        ((-4437600199 : Dyadic) * half ^ 34)⟩,
       ⟨((3884962753 : Dyadic) * half ^ 36),
        ((-2542755705 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((21935403097 : Dyadic) * half ^ 36),
        ((9754318087 : Dyadic) * half ^ 35)⟩,
       ⟨((6862861217 : Dyadic) * half ^ 35),
        ((-34746431461 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word9Step46 :
    word9Chunk46.foldl (fun acc a => a.applyPacked acc)
      word9State46 = word9State47 := by decide +kernel

private def word9Chunk47 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word9State48 : PackedMat2 :=
    ⟨⟨⟨((-8283203675 : Dyadic) * half ^ 37),
        ((6531338701 : Dyadic) * half ^ 35)⟩,
       ⟨((-41528930733 : Dyadic) * half ^ 37),
        ((3798886817 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1081270087 : Dyadic) * half ^ 37),
        ((30230770597 : Dyadic) * half ^ 37)⟩,
       ⟨((107996857101 : Dyadic) * half ^ 37),
        ((13992989827 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-5527970053 : Dyadic) * half ^ 34),
        ((-53457793507 : Dyadic) * half ^ 37)⟩,
       ⟨((-8118890385 : Dyadic) * half ^ 36),
        ((27269531797 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((14129112335 : Dyadic) * half ^ 35),
        ((-6226516801 : Dyadic) * half ^ 35)⟩,
       ⟨((-1066434933 : Dyadic) * half ^ 35),
        ((16622863529 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word9Step47 :
    word9Chunk47.foldl (fun acc a => a.applyPacked acc)
      word9State47 = word9State48 := by decide +kernel

private def word9Chunk48 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word9State49 : PackedMat2 :=
    ⟨⟨⟨((46627664763 : Dyadic) * half ^ 38),
        ((-8765544551 : Dyadic) * half ^ 35)⟩,
       ⟨((197759033499 : Dyadic) * half ^ 38),
        ((-15178817109 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-98961009919 : Dyadic) * half ^ 38),
        ((-36318734607 : Dyadic) * half ^ 37)⟩,
       ⟨((-23325436031 : Dyadic) * half ^ 38),
        ((39304479741 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-98961009919 : Dyadic) * half ^ 38),
        ((-36318734607 : Dyadic) * half ^ 37)⟩,
       ⟨((23325436031 : Dyadic) * half ^ 38),
        ((-39304479741 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-46627664763 : Dyadic) * half ^ 38),
        ((8765544551 : Dyadic) * half ^ 35)⟩,
       ⟨((197759033499 : Dyadic) * half ^ 38),
        ((-15178817109 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word9Step48 :
    word9Chunk48.foldl (fun acc a => a.applyPacked acc)
      word9State48 = word9State49 := by decide +kernel

private def word9Chunk49 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word9State50 : PackedMat2 :=
    ⟨⟨⟨((-102818546629 : Dyadic) * half ^ 37),
        ((-28080297795 : Dyadic) * half ^ 39)⟩,
       ⟨((-50775388195 : Dyadic) * half ^ 37),
        ((128391032807 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((32645018147 : Dyadic) * half ^ 38),
        ((71080886897 : Dyadic) * half ^ 39)⟩,
       ⟨((-97135868439 : Dyadic) * half ^ 38),
        ((-50891822799 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-1905823589 : Dyadic) * half ^ 33),
        ((-64890443293 : Dyadic) * half ^ 38)⟩,
       ⟨((10094532049 : Dyadic) * half ^ 38),
        ((-16122712573 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-78235665301 : Dyadic) * half ^ 38),
        ((-26021579217 : Dyadic) * half ^ 37)⟩,
       ⟨((-25077683753 : Dyadic) * half ^ 37),
        ((19199241853 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word9Step49 :
    word9Chunk49.foldl (fun acc a => a.applyPacked acc)
      word9State49 = word9State50 := by decide +kernel

private def word9Chunk50 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word9State51 : PackedMat2 :=
    ⟨⟨⟨((-315076254349 : Dyadic) * half ^ 39),
        ((-55997793597 : Dyadic) * half ^ 39)⟩,
       ⟨((-74633714989 : Dyadic) * half ^ 37),
        ((-27716014823 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-23702019597 : Dyadic) * half ^ 37),
        ((5951707095 : Dyadic) * half ^ 34)⟩,
       ⟨((-131843859673 : Dyadic) * half ^ 39),
        ((59624577677 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-23702019597 : Dyadic) * half ^ 37),
        ((5951707095 : Dyadic) * half ^ 34)⟩,
       ⟨((131843859673 : Dyadic) * half ^ 39),
        ((-59624577677 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((315076254349 : Dyadic) * half ^ 39),
        ((55997793597 : Dyadic) * half ^ 39)⟩,
       ⟨((-74633714989 : Dyadic) * half ^ 37),
        ((-27716014823 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word9Step50 :
    word9Chunk50.foldl (fun acc a => a.applyPacked acc)
      word9State50 = word9State51 := by decide +kernel

private def word9Chunk51 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word9State52 : PackedMat2 :=
    ⟨⟨⟨((-5447124425 : Dyadic) * half ^ 40),
        ((-1051083925933 : Dyadic) * half ^ 41)⟩,
       ⟨((-179293298801 : Dyadic) * half ^ 38),
        ((-31637067093 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-27961268347 : Dyadic) * half ^ 40),
        ((-76987426529 : Dyadic) * half ^ 41)⟩,
       ⟨((-14736781867 : Dyadic) * half ^ 38),
        ((518554657795 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-14736781867 : Dyadic) * half ^ 38),
        ((518554657795 : Dyadic) * half ^ 41)⟩,
       ⟨((-27961268347 : Dyadic) * half ^ 40),
        ((-76987426529 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((179293298801 : Dyadic) * half ^ 38),
        ((31637067093 : Dyadic) * half ^ 41)⟩,
       ⟨((5447124425 : Dyadic) * half ^ 40),
        ((1051083925933 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word9Step51 :
    word9Chunk51.foldl (fun acc a => a.applyPacked acc)
      word9State51 = word9State52 := by decide +kernel

private def word9Chunk52 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word9State53 : PackedMat2 :=
    ⟨⟨⟨((216840252921 : Dyadic) * half ^ 40),
        ((853769333995 : Dyadic) * half ^ 41)⟩,
       ⟨((-15925683487 : Dyadic) * half ^ 38),
        ((-427770329837 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((165248925083 : Dyadic) * half ^ 40),
        ((78009736871 : Dyadic) * half ^ 40)⟩,
       ⟨((380746452087 : Dyadic) * half ^ 40),
        ((-697088275459 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-380746452087 : Dyadic) * half ^ 40),
        ((697088275459 : Dyadic) * half ^ 41)⟩,
       ⟨((-165248925083 : Dyadic) * half ^ 40),
        ((-78009736871 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-15925683487 : Dyadic) * half ^ 38),
        ((-427770329837 : Dyadic) * half ^ 40)⟩,
       ⟨((216840252921 : Dyadic) * half ^ 40),
        ((853769333995 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word9Step52 :
    word9Chunk52.foldl (fun acc a => a.applyPacked acc)
      word9State52 = word9State53 := by decide +kernel

private def word9Chunk53 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word9State54 : PackedMat2 :=
    ⟨⟨⟨((981836386685 : Dyadic) * half ^ 42),
        ((188089836565 : Dyadic) * half ^ 39)⟩,
       ⟨((-1818469615223 : Dyadic) * half ^ 42),
        ((1272359243269 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1259856036979 : Dyadic) * half ^ 42),
        ((654064556247 : Dyadic) * half ^ 41)⟩,
       ⟨((-1061907375073 : Dyadic) * half ^ 42),
        ((764374858943 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1259856036979 : Dyadic) * half ^ 42),
        ((654064556247 : Dyadic) * half ^ 41)⟩,
       ⟨((1061907375073 : Dyadic) * half ^ 42),
        ((-764374858943 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-981836386685 : Dyadic) * half ^ 42),
        ((-188089836565 : Dyadic) * half ^ 39)⟩,
       ⟨((-1818469615223 : Dyadic) * half ^ 42),
        ((1272359243269 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word9Step53 :
    word9Chunk53.foldl (fun acc a => a.applyPacked acc)
      word9State53 = word9State54 := by decide +kernel

private def word9Chunk54 : List Letter := [.h]
private def word9State55 : PackedMat2 :=
    ⟨⟨⟨((1406423902507 : Dyadic) * half ^ 41),
        ((140105776479 : Dyadic) * half ^ 39)⟩,
       ⟨((253992192163 : Dyadic) * half ^ 41),
        ((-378281120075 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-98294790013 : Dyadic) * half ^ 41),
        ((139009825147 : Dyadic) * half ^ 42)⟩,
       ⟨((509183525553 : Dyadic) * half ^ 40),
        ((-360047123787 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((98294790013 : Dyadic) * half ^ 41),
        ((-139009825147 : Dyadic) * half ^ 42)⟩,
       ⟨((509183525553 : Dyadic) * half ^ 40),
        ((-360047123787 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((1406423902507 : Dyadic) * half ^ 41),
        ((140105776479 : Dyadic) * half ^ 39)⟩,
       ⟨((-253992192163 : Dyadic) * half ^ 41),
        ((378281120075 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word9Step54 :
    word9Chunk54.foldl (fun acc a => a.applyPacked acc)
      word9State54 = word9State55 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word9_check : check word9 9 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word9 = word9State55.toMatrix := by
    unfold evalRingPacked
    change ((
      word9Chunk0 ++ word9Chunk1 ++ word9Chunk2 ++ word9Chunk3 ++
      word9Chunk4 ++ word9Chunk5 ++ word9Chunk6 ++ word9Chunk7 ++
      word9Chunk8 ++ word9Chunk9 ++ word9Chunk10 ++ word9Chunk11 ++
      word9Chunk12 ++ word9Chunk13 ++ word9Chunk14 ++ word9Chunk15 ++
      word9Chunk16 ++ word9Chunk17 ++ word9Chunk18 ++ word9Chunk19 ++
      word9Chunk20 ++ word9Chunk21 ++ word9Chunk22 ++ word9Chunk23 ++
      word9Chunk24 ++ word9Chunk25 ++ word9Chunk26 ++ word9Chunk27 ++
      word9Chunk28 ++ word9Chunk29 ++ word9Chunk30 ++ word9Chunk31 ++
      word9Chunk32 ++ word9Chunk33 ++ word9Chunk34 ++ word9Chunk35 ++
      word9Chunk36 ++ word9Chunk37 ++ word9Chunk38 ++ word9Chunk39 ++
      word9Chunk40 ++ word9Chunk41 ++ word9Chunk42 ++ word9Chunk43 ++
      word9Chunk44 ++ word9Chunk45 ++ word9Chunk46 ++ word9Chunk47 ++
      word9Chunk48 ++ word9Chunk49 ++ word9Chunk50 ++ word9Chunk51 ++
      word9Chunk52 ++ word9Chunk53 ++ word9Chunk54
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word9Step0, word9Step1, word9Step2, word9Step3, word9Step4,
      word9Step5, word9Step6, word9Step7, word9Step8, word9Step9,
      word9Step10, word9Step11, word9Step12, word9Step13, word9Step14,
      word9Step15, word9Step16, word9Step17, word9Step18, word9Step19,
      word9Step20, word9Step21, word9Step22, word9Step23, word9Step24,
      word9Step25, word9Step26, word9Step27, word9Step28, word9Step29,
      word9Step30, word9Step31, word9Step32, word9Step33, word9Step34,
      word9Step35, word9Step36, word9Step37, word9Step38, word9Step39,
      word9Step40, word9Step41, word9Step42, word9Step43, word9Step44,
      word9Step45, word9Step46, word9Step47, word9Step48, word9Step49,
      word9Step50, word9Step51, word9Step52, word9Step53, word9Step54]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
