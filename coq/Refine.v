(** * General refinement (T1) in Coq -- mirror of lean/Hex0/Refine.lean.

    Proof-grade theorem: for ALL inputs, the real `core` computes `coreSpec`.
    No vm_compute on the general statement -- it is genuine induction.

    STATUS: the FOUNDATION TIER is ported and proved (kernel-checked), mirroring
    `lean/Hex0/Refine.lean` §5 up to (and including) the EOF base case:
      - `fetch_code` + all 12 `step_*` lemmas + state/storeByte projections
        (`decode (wordAt off)` reduces under `vm_compute` at concrete offsets, so
        the step lemmas apply exactly as in Lean);
      - arithmetic toolkit: `wrap_small`, `wadd_id`, `toS_small`, `sltb_small`;
      - `runUntil` composition: `runUntil_halt`, `runUntil_one`, `runUntil_S`,
        `runUntil_add`;
      - spec-side token decomposition: `decodeS_spacing`/`byte`/`comment`;
      - `core_eof` -- the EOF base case (4-step run to a correct halt).
    Remaining frontier (the large tail, `Admitted`): `LoopInv` + the per-token
    dispatch (`loop_iteration`) + induction (`loop_correct`) + prologue + the
    `runOn↔coreSpec` conversion. Two Coq-specific notes vs Lean (see PROOF.md §8):
    (1) `runOn` uses a *fixed* fuel (100000), so the assembly needs a step-count
    bound (Lean used ∃fuel); (2) the model's bytes are `Z` but the spec is on
    `nat`, so `LoopInv`/dispatch carry `Z.of_nat`/`Z.to_nat` (`zin`) conversions. *)

From Coq Require Import ZArith List Lia Bool.
From Equations Require Import Equations.
From Hex0Coq Require Import Spec Rv64i Image Harness.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Per-step reduction primitive (PROVED).
    `core`'s first instruction `li t0,0` = `addi x5,x0,0`, bytes 93 02 00 00,
    word 0x293 = 659. One [step] computes its effect; data stays symbolic. *)
Theorem step_li_t0 : forall s,
  s.(mem) s.(pc) = 147 ->
  s.(mem) (s.(pc) + 1) = 2 ->
  s.(mem) (s.(pc) + 2) = 0 ->
  s.(mem) (s.(pc) + 3) = 0 ->
  s.(pc) = 2147483784 ->
  (step s).(pc) = 2147483788 /\ rget (step s) 5 = 0.
Proof.
  intros s h0 h1 h2 h3 hpc.
  unfold step, fetch32.
  rewrite h0, h1, h2, h3.
  (* fetched word is now the closed value 659; decode + effect compute *)
  change (147 + 2 * 256 + 0 * 65536 + 0 * 16777216) with 659.
  rewrite hpc. cbn. split; reflexivity.
Qed.

(** ** Engine: fetch at a code offset + per-instruction step lemmas.
    Mirror of `Refine.lean`'s `fetch_code` + `step_*`. Words are [Z]; the
    decode of a closed word reduces under [cbn]/[vm_compute] at call sites. *)

Definition nthb (i : Z) : Z := nth (Z.to_nat i) coreBytes 0.

Definition wordAt (off : Z) : Z :=
  nthb off + nthb (off + 1) * 256 + nthb (off + 2) * 65536 + nthb (off + 3) * 16777216.

Definition CodeLoaded (s : State) : Prop :=
  forall i, 0 <= i < Z.of_nat (length coreBytes) -> s.(mem) (coreAddr + i) = nthb i.

(* state projections *)
Lemma setPc_pc s p : (setPc s p).(pc) = p. Proof. reflexivity. Qed.
Lemma setPc_mem s p : (setPc s p).(mem) = s.(mem). Proof. reflexivity. Qed.
Lemma setPc_rget s p i : rget (setPc s p) i = rget s i. Proof. reflexivity. Qed.
Lemma rset_pc s rd v : (rset s rd v).(pc) = s.(pc).
Proof. unfold rset; destruct (rd =? 0); reflexivity. Qed.
Lemma rset_mem s rd v : (rset s rd v).(mem) = s.(mem).
Proof. unfold rset; destruct (rd =? 0); reflexivity. Qed.
Lemma rget_zero s : rget s 0 = 0. Proof. reflexivity. Qed.

Lemma rset_rget s rd v i : rd <> 0 -> i <> 0 ->
  rget (rset s rd v) i = if i =? rd then v else rget s i.
Proof.
  intros hrd hi. unfold rget, rset.
  destruct (rd =? 0) eqn:Erd; [apply Z.eqb_eq in Erd; lia|].
  destruct (i =? 0) eqn:Ei; [apply Z.eqb_eq in Ei; lia|].
  reflexivity.
Qed.

Lemma fetch_code : forall s off,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> fetch32 s = wordAt off.
Proof.
  intros s off hc ho1 ho2 hpc.
  unfold fetch32, wordAt. rewrite hpc.
  replace (coreAddr + off + 1) with (coreAddr + (off + 1)) by lia.
  replace (coreAddr + off + 2) with (coreAddr + (off + 2)) by lia.
  replace (coreAddr + off + 3) with (coreAddr + (off + 3)) by lia.
  rewrite (hc off ltac:(lia)), (hc (off+1) ltac:(lia)),
          (hc (off+2) ltac:(lia)), (hc (off+3) ltac:(lia)).
  reflexivity.
Qed.

Lemma step_addi : forall s off rd rs1 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Iaddi rd rs1 imm ->
  step s = setPc (rset s rd (wadd (rget s rs1) imm)) (wadd s.(pc) 4).
Proof.
  intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity.
Qed.

Lemma step_bgeu : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ibgeu rs1 rs2 imm ->
  step s = setPc s (if ultb (rget s rs1) (rget s rs2) then wadd s.(pc) 4 else wadd s.(pc) imm).
Proof.
  intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity.
Qed.

Lemma step_add : forall s off rd rs1 rs2,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Iadd rd rs1 rs2 ->
  step s = setPc (rset s rd (wadd (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_or : forall s off rd rs1 rs2,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ior rd rs1 rs2 ->
  step s = setPc (rset s rd (wor (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_slli : forall s off rd rs1 sh,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Islli rd rs1 sh ->
  step s = setPc (rset s rd (wshl (rget s rs1) sh)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 sh hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_lbu : forall s off rd rs1 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ilbu rd rs1 imm ->
  step s = setPc (rset s rd ((s.(mem) (wadd (rget s rs1) imm)) mod 256)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_sb : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Isb rs1 rs2 imm ->
  step s = setPc (storeByte s (wadd (rget s rs1) imm) (rget s rs2)) (wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_beq : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ibeq rs1 rs2 imm ->
  step s = setPc s (if (rget s rs1) =? (rget s rs2) then wadd s.(pc) imm else wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_blt : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Iblt rs1 rs2 imm ->
  step s = setPc s (if sltb (rget s rs1) (rget s rs2) then wadd s.(pc) imm else wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_bge : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ibge rs1 rs2 imm ->
  step s = setPc s (if sltb (rget s rs1) (rget s rs2) then wadd s.(pc) 4 else wadd s.(pc) imm).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_jal : forall s off rd imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ijal rd imm ->
  step s = setPc (rset s rd (wadd s.(pc) 4)) (wadd s.(pc) imm).
Proof. intros s off rd imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_jalr : forall s off rd rs1 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ijalr rd rs1 imm ->
  step s = setPc (rset s rd (wadd s.(pc) 4))
                 (wadd (rget s rs1) imm - (wadd (rget s rs1) imm) mod 2).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

(* storeByte touches only memory *)
Lemma storeByte_pc s a b : (storeByte s a b).(pc) = s.(pc). Proof. reflexivity. Qed.
Lemma storeByte_reg s a b : (storeByte s a b).(reg) = s.(reg). Proof. reflexivity. Qed.
Lemma storeByte_rget s a b i : rget (storeByte s a b) i = rget s i. Proof. reflexivity. Qed.
Lemma storeByte_mem s a b : (storeByte s a b).(mem) = (fun x => if x =? a then b mod 256 else s.(mem) x).
Proof. reflexivity. Qed.

(** ** Arithmetic toolkit (mirror of ult_ofNat/slt_ofNat/ofNat_ne/setWidth8). *)

Lemma wrap_small z : 0 <= z < 2 ^ 64 -> wrap z = z.
Proof. unfold wrap, w64. apply Z.mod_small. Qed.

(* address arithmetic with no 64-bit wraparound *)
Lemma wadd_id a b : 0 <= a + b < 2 ^ 64 -> wadd a b = a + b.
Proof. unfold wadd. apply wrap_small. Qed.

Lemma toS_small x : 0 <= x < 2 ^ 63 -> toS x = x.
Proof. unfold toS. intros h. destruct (x >=? 2 ^ 63) eqn:E; [lia | reflexivity]. Qed.

(* signed compare = unsigned compare on small (< 2^63) values *)
Lemma sltb_small a b : 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> sltb a b = (a <? b).
Proof. intros ha hb. unfold sltb. rewrite (toS_small a ha), (toS_small b hb). reflexivity. Qed.

(** ** runUntil (= Lean runFuel) composition. *)

Lemma runUntil_halt n s : s.(pc) = 0 -> runUntil 0 n s = s.
Proof. intros h. destruct n; [reflexivity|]. simpl. rewrite h, Z.eqb_refl. reflexivity. Qed.

Lemma runUntil_one s : s.(pc) <> 0 -> runUntil 0 1 s = step s.
Proof.
  intros h. simpl. destruct (s.(pc) =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.

Lemma runUntil_S n s : s.(pc) <> 0 -> runUntil 0 (S n) s = runUntil 0 n (step s).
Proof.
  intros h. simpl. destruct (s.(pc) =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.

Lemma runUntil_add a b s : runUntil 0 (a + b) s = runUntil 0 b (runUntil 0 a s).
Proof.
  revert b s. induction a as [|k ih]; intros b s; simpl; [reflexivity|].
  destruct (s.(pc) =? 0) eqn:E.
  - apply Z.eqb_eq in E. now rewrite (runUntil_halt b s E).
  - apply ih.
Qed.

(** ** Spec-side token decomposition (mirror of decodeS_spacing/byte/comment). *)

Lemma decodeS_spacing c rest : isComment c = false -> isSpace c = true ->
  decodeS High (c :: rest) = decodeS High rest.
Proof. intros hc hs. simp decodeS. rewrite hc, hs. reflexivity. Qed.

Lemma decodeS_byte chi clo rest hi lo :
  isComment chi = false -> isSpace chi = false -> nibble chi = Some hi ->
  isLowStop clo = false -> nibble clo = Some lo ->
  decodeS High (chi :: clo :: rest) =
    ((hi * 16 + lo)%nat :: fst (decodeS High rest), snd (decodeS High rest)).
Proof.
  intros hc hs hh hlc hl. simp decodeS. rewrite hc, hs, hh. simp decodeS. rewrite hlc, hl.
  destruct (decodeS High rest) as [out st]. reflexivity.
Qed.

Lemma decodeS_comment c rest : isComment c = true ->
  decodeS High (c :: rest) = decodeS High (skipComment rest).
Proof. intros hc. simp decodeS. rewrite hc. reflexivity. Qed.

(** ** EOF base case (mirror of core_eof). *)

Lemma coreBytes_len : Z.of_nat (length coreBytes) = 324. Proof. reflexivity. Qed.
Lemma coreAddr_pos k : 0 <= k -> coreAddr + k <> 0. Proof. unfold coreAddr; lia. Qed.
Lemma CodeLoaded_eqmem s t : t.(mem) = s.(mem) -> CodeLoaded s -> CodeLoaded t.
Proof. intros hm hcs i Hi. rewrite hm. apply hcs; exact Hi. Qed.

Lemma core_eof : forall s L E,
  CodeLoaded s -> s.(pc) = coreAddr + 8 ->
  rget s 5 = L -> rget s 11 = L -> rget s 6 = E -> rget s 1 = 0 -> 0 <= E < 2 ^ 64 ->
  (runUntil 0 4 s).(pc) = 0 /\ rget (runUntil 0 4 s) 10 = 0 /\
  rget (runUntil 0 4 s) 11 = E /\ (runUntil 0 4 s).(mem) = s.(mem).
Proof.
  intros s L E hc hpc h5 h11 h6 h1 hE.
  (* step 1: bgeu t0,a1 taken (t0 = a1) -> .Lok (264) *)
  assert (hs1 : step s = setPc s (coreAddr + 264)).
  { rewrite (step_bgeu s 8 5 11 256 hc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc
              ltac:(vm_compute; reflexivity)).
    rewrite h5, h11. unfold ultb. rewrite Z.ltb_irrefl. cbn match.
    rewrite hpc, (wadd_id (coreAddr+8) 256 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s1 := setPc s (coreAddr + 264)) in *.
  assert (hpc1 : s1.(pc) = coreAddr + 264) by (unfold s1; apply setPc_pc).
  assert (hc1 : CodeLoaded s1) by (apply (CodeLoaded_eqmem s); [reflexivity| exact hc]).
  (* step 2: li a0,0 -> 268 *)
  assert (hs2 : step s1 = setPc (rset s1 10 0) (coreAddr + 268)).
  { rewrite (step_addi s1 264 10 0 0 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1
              ltac:(vm_compute; reflexivity)).
    rewrite rget_zero, (wadd_id 0 0 ltac:(lia)), hpc1,
            (wadd_id (coreAddr+264) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s2 := setPc (rset s1 10 0) (coreAddr + 268)) in *.
  assert (hpc2 : s2.(pc) = coreAddr + 268) by (unfold s2; apply setPc_pc).
  assert (hc2 : CodeLoaded s2) by
    (apply (CodeLoaded_eqmem s); [unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem; reflexivity| exact hc]).
  assert (h6_2 : rget s2 6 = E).
  { unfold s2. rewrite setPc_rget, (rset_rget s1 10 0 6 ltac:(lia) ltac:(lia)).
    unfold s1. rewrite setPc_rget. exact h6. }
  (* step 3: mv a1,t1 -> 272 *)
  assert (hs3 : step s2 = setPc (rset s2 11 E) (coreAddr + 272)).
  { rewrite (step_addi s2 268 11 6 0 hc2 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc2
              ltac:(vm_compute; reflexivity)).
    rewrite h6_2, (wadd_id E 0 ltac:(lia)), Z.add_0_r, hpc2,
            (wadd_id (coreAddr+268) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s3 := setPc (rset s2 11 E) (coreAddr + 272)) in *.
  assert (hpc3 : s3.(pc) = coreAddr + 272) by (unfold s3; apply setPc_pc).
  assert (hc3 : CodeLoaded s3) by
    (apply (CodeLoaded_eqmem s); [unfold s3,s2,s1; rewrite !setPc_mem, !rset_mem; reflexivity| exact hc]).
  assert (h1_3 : rget s3 1 = 0).
  { unfold s3. rewrite setPc_rget, (rset_rget s2 11 E 1 ltac:(lia) ltac:(lia)).
    unfold s2. rewrite setPc_rget, (rset_rget s1 10 0 1 ltac:(lia) ltac:(lia)).
    unfold s1. rewrite setPc_rget. exact h1. }
  (* step 4: ret -> pc = 0 *)
  assert (hs4 : step s3 = setPc s3 0).
  { rewrite (step_jalr s3 272 0 1 0 hc3 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc3
              ltac:(vm_compute; reflexivity)).
    assert (Hr : rset s3 0 (wadd s3.(pc) 4) = s3) by (unfold rset; reflexivity).
    rewrite Hr, h1_3, (wadd_id 0 0 ltac:(lia)). reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; apply coreAddr_pos; lia).
  assert (hp3 : s3.(pc) <> 0) by (rewrite hpc3; apply coreAddr_pos; lia).
  assert (hrun : runUntil 0 4 s = setPc s3 0).
  { rewrite (runUntil_S 3 s hp0), hs1, (runUntil_S 2 s1 hp1), hs2,
            (runUntil_S 1 s2 hp2), hs3, (runUntil_S 0 s3 hp3), hs4. reflexivity. }
  rewrite hrun. refine (conj _ (conj _ (conj _ _))).
  - rewrite setPc_pc. reflexivity.
  - rewrite setPc_rget. unfold s3. rewrite setPc_rget, (rset_rget s2 11 E 10 ltac:(lia) ltac:(lia)).
    unfold s2. rewrite setPc_rget, (rset_rget s1 10 0 10 ltac:(lia) ltac:(lia)). reflexivity.
  - rewrite setPc_rget. unfold s3. rewrite setPc_rget, (rset_rget s2 11 E 11 ltac:(lia) ltac:(lia)).
    reflexivity.
  - rewrite setPc_mem. unfold s3, s2, s1. rewrite !setPc_mem, !rset_mem. reflexivity.
Qed.

(** ** Well-formedness: input region fits before the output region, etc. *)
Record WellFormed (inp : list Z) (cap : Z) : Prop := {
  in_fits  : inputAddr + Z.of_nat (length inp) <= outAddr;
  out_fits : outAddr + cap < 2 ^ 64;
  bytes_ok : forall b, In b inp -> 0 <= b < 256
}.

(** ** The general refinement theorem (FRONTIER).
    Proof outline (mirrors the Lean file): establish the main-loop invariant from
    the initial state, prove one iteration preserves it or halts correctly (case
    analysis on the next char's class), induct on the remaining input length. *)
Theorem core_refines : forall (inp : list Z) (cap : Z),
  WellFormed inp cap ->
  runOn inp cap = specOn (zin inp) (Z.to_nat cap).
Proof.
Admitted.
