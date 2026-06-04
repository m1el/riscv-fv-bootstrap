(** * General refinement for hex1 in Coq -- mirror of lean/Hex1/Refine.lean.

    Target (the Coq port of the campaign theorem, cf. Refine.v for hex0):

      core1_refines : forall inp cap, WellFormed1 inp cap ->
        runOn1-style observation of the real core1 bytes = coreSpec1 inp cap

    proved by genuine induction (no vm_compute on the general statement),
    over the THREE loops of core1 (init / pass 1 / pass 2) and the label
    table region.

    STATUS: IN PROGRESS -- engine layer (chunk 1).
    - fetch at a code offset (Image1) + the 16 per-instruction step lemmas
      (hex0's 12 + SUB SRLI LD SD);
    - storeWord/loadWord state projections, per-byte reads, the frame
      lemma, and the 8-digit reassembly [loadWord_storeWord];
    - the wsub/wshr arithmetic bridges.
    The generic toolkit (state projections, wrap_small/wadd_id/toS_small/
    sltb_small, runUntil composition incl. runUntil_stab) is REUSED from
    the hex0 port (Hex0Coq.Refine) -- those lemmas are Image-independent. *)

From Coq Require Import ZArith List Lia Bool.
From Equations Require Import Equations.
From Hex0Coq Require Import Spec1 Rv64i Harness1 Refine.
From Hex0Coq Require Image1.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Engine: fetch at a code offset + per-instruction step lemmas
    (Image1 versions; mirror of lean/Hex1/RefineBase.lean). *)

Definition nthb1 (i : Z) : Z := nth (Z.to_nat i) Image1.coreBytes 0.

Definition wordAt1 (off : Z) : Z :=
  nthb1 off + nthb1 (off + 1) * 256 + nthb1 (off + 2) * 65536 + nthb1 (off + 3) * 16777216.

Definition CodeLoaded1 (s : State) : Prop :=
  forall i, 0 <= i < Z.of_nat (length Image1.coreBytes) ->
    s.(mem) (Image1.coreAddr + i) = nthb1 i.

Lemma coreBytes1_len : Z.of_nat (length Image1.coreBytes) = 724.
Proof. reflexivity. Qed.
Lemma coreAddr1_pos k : 0 <= k -> Image1.coreAddr + k <> 0.
Proof. unfold Image1.coreAddr; lia. Qed.
Lemma CodeLoaded1_eqmem s t : t.(mem) = s.(mem) -> CodeLoaded1 s -> CodeLoaded1 t.
Proof. intros He H i Hi. rewrite He. exact (H i Hi). Qed.

Lemma fetch_code1 : forall s off,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> fetch32 s = wordAt1 off.
Proof.
  intros s off hc ho1 ho2 hpc.
  unfold fetch32, wordAt1. rewrite hpc.
  replace (Image1.coreAddr + off + 1) with (Image1.coreAddr + (off + 1)) by lia.
  replace (Image1.coreAddr + off + 2) with (Image1.coreAddr + (off + 2)) by lia.
  replace (Image1.coreAddr + off + 3) with (Image1.coreAddr + (off + 3)) by lia.
  rewrite (hc off ltac:(lia)), (hc (off+1) ltac:(lia)),
          (hc (off+2) ltac:(lia)), (hc (off+3) ltac:(lia)).
  reflexivity.
Qed.

(* the 16 per-instruction step lemmas, all the same one-line proof *)
Lemma step1_addi : forall s off rd rs1 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Iaddi rd rs1 imm ->
  step s = setPc (rset s rd (wadd (rget s rs1) imm)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_add : forall s off rd rs1 rs2,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Iadd rd rs1 rs2 ->
  step s = setPc (rset s rd (wadd (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_sub : forall s off rd rs1 rs2,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Isub rd rs1 rs2 ->
  step s = setPc (rset s rd (wsub (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_or : forall s off rd rs1 rs2,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ior rd rs1 rs2 ->
  step s = setPc (rset s rd (wor (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_slli : forall s off rd rs1 sh,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Islli rd rs1 sh ->
  step s = setPc (rset s rd (wshl (rget s rs1) sh)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 sh hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_srli : forall s off rd rs1 sh,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Isrli rd rs1 sh ->
  step s = setPc (rset s rd (wshr (rget s rs1) sh)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 sh hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_lbu : forall s off rd rs1 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ilbu rd rs1 imm ->
  step s = setPc (rset s rd ((s.(mem) (wadd (rget s rs1) imm)) mod 256)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_ld : forall s off rd rs1 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ild rd rs1 imm ->
  step s = setPc (rset s rd (loadWord s (wadd (rget s rs1) imm))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_sb : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Isb rs1 rs2 imm ->
  step s = setPc (storeByte s (wadd (rget s rs1) imm) (rget s rs2)) (wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_sd : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Isd rs1 rs2 imm ->
  step s = setPc (storeWord s (wadd (rget s rs1) imm) (rget s rs2)) (wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_beq : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ibeq rs1 rs2 imm ->
  step s = setPc s (if (rget s rs1) =? (rget s rs2) then wadd s.(pc) imm else wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_blt : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Iblt rs1 rs2 imm ->
  step s = setPc s (if sltb (rget s rs1) (rget s rs2) then wadd s.(pc) imm else wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_bge : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ibge rs1 rs2 imm ->
  step s = setPc s (if sltb (rget s rs1) (rget s rs2) then wadd s.(pc) 4 else wadd s.(pc) imm).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_bgeu : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ibgeu rs1 rs2 imm ->
  step s = setPc s (if ultb (rget s rs1) (rget s rs2) then wadd s.(pc) 4 else wadd s.(pc) imm).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_jal : forall s off rd imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ijal rd imm ->
  step s = setPc (rset s rd (wadd s.(pc) 4)) (wadd s.(pc) imm).
Proof. intros s off rd imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_jalr : forall s off rd rs1 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ijalr rd rs1 imm ->
  step s = setPc (rset s rd (wadd s.(pc) 4))
                 (wadd (rget s rs1) imm - (wadd (rget s rs1) imm) mod 2).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

(** ** storeWord / loadWord state lemmas (mirror of RefineBase.lean's
    storeWord_pc/rget/frame/get0..7 + assemble_bytes; addresses are [Z],
    so distinctness is just [lia]). *)

Lemma storeWord_pc s a v : (storeWord s a v).(pc) = s.(pc).
Proof. reflexivity. Qed.
Lemma storeWord_reg s a v : (storeWord s a v).(reg) = s.(reg).
Proof. reflexivity. Qed.
Lemma storeWord_rget s a v i : rget (storeWord s a v) i = rget s i.
Proof. reflexivity. Qed.

(* the full byte map of an 8-byte store (outermost test = last store, a+7) *)
Lemma storeWord_mem_at : forall s a v x,
  (storeWord s a v).(mem) x =
  (if x =? a + 7 then (v / 2 ^ 56) mod 256
   else if x =? a + 6 then (v / 2 ^ 48) mod 256
   else if x =? a + 5 then (v / 2 ^ 40) mod 256
   else if x =? a + 4 then (v / 2 ^ 32) mod 256
   else if x =? a + 3 then (v / 2 ^ 24) mod 256
   else if x =? a + 2 then (v / 2 ^ 16) mod 256
   else if x =? a + 1 then (v / 2 ^ 8) mod 256
   else if x =? a then v mod 256
   else s.(mem) x).
Proof. reflexivity. Qed.

(* reading outside the 8 stored bytes is unchanged *)
Lemma storeWord_frame : forall s a v x,
  (forall k, 0 <= k < 8 -> x <> a + k) ->
  (storeWord s a v).(mem) x = s.(mem) x.
Proof.
  intros s a v x h. rewrite storeWord_mem_at.
  pose proof (h 0 ltac:(lia)). pose proof (h 1 ltac:(lia)).
  pose proof (h 2 ltac:(lia)). pose proof (h 3 ltac:(lia)).
  pose proof (h 4 ltac:(lia)). pose proof (h 5 ltac:(lia)).
  pose proof (h 6 ltac:(lia)). pose proof (h 7 ltac:(lia)).
  repeat (rewrite (proj2 (Z.eqb_neq _ _)) by lia). reflexivity.
Qed.

(* per-byte reads of the stored word: byte k of [storeWord s a v] at a+k *)
Lemma storeWord_get : forall s a v k, 0 <= k < 8 ->
  (storeWord s a v).(mem) (a + k) = (v / 2 ^ (8 * k)) mod 256.
Proof.
  intros s a v k hk.
  assert (hk8 : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  destruct hk8 as [->| [->| [->| [->| [->| [->| [->| ->]]]]]]];
    [ replace (a + 0) with a by lia | | | | | | | ];
    rewrite storeWord_mem_at;
    repeat (rewrite (proj2 (Z.eqb_neq _ _)) by lia);
    rewrite Z.eqb_refl;
    try reflexivity.
  (* k = 0: 8*0 = 0; v / 2^0 = v *)
  now rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
Qed.

(* the base-256 digit reassembly: loadWord after storeWord at the same
   address returns the stored (in-range) value (Lean's assemble_bytes). *)
Lemma digits8 : forall v, 0 <= v < 2 ^ 64 ->
  v mod 256
  + (v / 2 ^ 8) mod 256 * 2 ^ 8
  + (v / 2 ^ 16) mod 256 * 2 ^ 16
  + (v / 2 ^ 24) mod 256 * 2 ^ 24
  + (v / 2 ^ 32) mod 256 * 2 ^ 32
  + (v / 2 ^ 40) mod 256 * 2 ^ 40
  + (v / 2 ^ 48) mod 256 * 2 ^ 48
  + (v / 2 ^ 56) mod 256 * 2 ^ 56 = v.
Proof.
  intros v hv.
  replace (v / 2 ^ 16) with (v / 2 ^ 8 / 2 ^ 8) by (rewrite Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 24) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 32) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 40) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 48) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 56) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  set (x1 := v / 2 ^ 8). set (x2 := x1 / 2 ^ 8). set (x3 := x2 / 2 ^ 8).
  set (x4 := x3 / 2 ^ 8). set (x5 := x4 / 2 ^ 8). set (x6 := x5 / 2 ^ 8).
  set (x7 := x6 / 2 ^ 8).
  pose proof (Z.div_mod v (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x1 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x2 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x3 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x4 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x5 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x6 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound v (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x1 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x2 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x3 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x4 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x5 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x6 (2 ^ 8) ltac:(lia)).
  assert (hx7 : x7 = v / 2 ^ 56).
  { unfold x7, x6, x5, x4, x3, x2, x1. rewrite !Z.div_div by lia. reflexivity. }
  assert (hx7b : 0 <= x7 < 2 ^ 8).
  { rewrite hx7. split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia. }
  assert (hx7m : x7 mod 256 = x7) by (apply Z.mod_small; lia).
  rewrite hx7m.
  change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536.
  change (2 ^ 24) with 16777216. change (2 ^ 32) with 4294967296.
  change (2 ^ 40) with 1099511627776. change (2 ^ 48) with 281474976710656.
  change (2 ^ 56) with 72057594037927936.
  lia.
Qed.

Lemma loadWord_storeWord : forall s a v, 0 <= v < 2 ^ 64 ->
  loadWord (storeWord s a v) a = v.
Proof.
  intros s a v hv. unfold loadWord.
  pose proof (storeWord_get s a v 0 ltac:(lia)) as G0.
  replace (a + 0) with a in G0 by lia.
  pose proof (storeWord_get s a v 1 ltac:(lia)) as G1.
  pose proof (storeWord_get s a v 2 ltac:(lia)) as G2.
  pose proof (storeWord_get s a v 3 ltac:(lia)) as G3.
  pose proof (storeWord_get s a v 4 ltac:(lia)) as G4.
  pose proof (storeWord_get s a v 5 ltac:(lia)) as G5.
  pose proof (storeWord_get s a v 6 ltac:(lia)) as G6.
  pose proof (storeWord_get s a v 7 ltac:(lia)) as G7.
  rewrite G0, G1, G2, G3, G4, G5, G6, G7.
  change (8 * 0) with 0. change (8 * 1) with 8. change (8 * 2) with 16.
  change (8 * 3) with 24. change (8 * 4) with 32. change (8 * 5) with 40.
  change (8 * 6) with 48. change (8 * 7) with 56.
  rewrite Z.pow_0_r, Z.div_1_r.
  apply digits8. exact hv.
Qed.

(** ** Arithmetic bridges for the new instructions. *)

(* sub with no underflow: the Z value *)
Lemma wsub_id a b : 0 <= a - b < 2 ^ 64 -> wsub a b = a - b.
Proof. unfold wsub. apply wrap_small. Qed.

(* logical shift right = division by 2^n *)
Lemma wshr_div a n : 0 <= n -> wshr a n = a / 2 ^ n.
Proof. intros hn. unfold wshr. apply Z.shiftr_div_pow2. exact hn. Qed.

(** ** Reusable [li t3,K; branch t2,t3] blocks (ports of the hex0 Coq ones,
    under [CodeLoaded1]). Each runs 2 steps, resolving the branch; clobbers
    only t3 (x28) and pc. *)

Lemma li1_beq_ne s off K c imm :
  CodeLoaded1 s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt1 off) = Iaddi 28 0 K ->
  decode (wordAt1 (off + 4)) = Ibeq 7 28 imm ->
  0 <= K < 2 ^ 64 ->
  c <> K ->
  runUntil 0 2 s = setPc (rset s 28 K) (Image1.coreAddr + (off + 8)).
Proof.
  intros hc ho hb hpc h7 hli hbeq hK hne.
  rewrite coreBytes1_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length Image1.coreBytes)) by (rewrite coreBytes1_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 7 ltac:(lia) ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)); reflexivity).
  assert (hu2 : step s1 = setPc s1 (Image1.coreAddr + (off + 8))).
  { rewrite (step1_beq s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hbeq), h7s1, h28s1.
    replace (c =? K) with false by (symmetry; apply Z.eqb_neq; exact hne).
    rewrite hpc1, (wadd_id (Image1.coreAddr + (off + 4)) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

Lemma li1_beq_eq s off K c imm target :
  CodeLoaded1 s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt1 off) = Iaddi 28 0 K ->
  decode (wordAt1 (off + 4)) = Ibeq 7 28 imm ->
  0 <= K < 2 ^ 64 ->
  c = K ->
  wadd (Image1.coreAddr + (off + 4)) imm = target ->
  runUntil 0 2 s = setPc (rset s 28 K) target.
Proof.
  intros hc ho hb hpc h7 hli hbeq hK heq htgt.
  rewrite coreBytes1_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length Image1.coreBytes)) by (rewrite coreBytes1_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 7 ltac:(lia) ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)); reflexivity).
  assert (hu2 : step s1 = setPc s1 target).
  { rewrite (step1_beq s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hbeq), h7s1, h28s1.
    replace (c =? K) with true by (symmetry; apply Z.eqb_eq; exact heq).
    rewrite hpc1, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

Lemma li1_blt_nt s off K c imm :
  CodeLoaded1 s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt1 off) = Iaddi 28 0 K ->
  decode (wordAt1 (off + 4)) = Iblt 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  ~ c < K ->
  runUntil 0 2 s = setPc (rset s 28 K) (Image1.coreAddr + (off + 8)).
Proof.
  intros hc ho hb hpc h7 hli hblt hK hc63 hge.
  rewrite coreBytes1_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length Image1.coreBytes)) by (rewrite coreBytes1_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 7 ltac:(lia) ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)); reflexivity).
  assert (hu2 : step s1 = setPc s1 (Image1.coreAddr + (off + 8))).
  { rewrite (step1_blt s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hblt), h7s1, h28s1.
    rewrite (sltb_small c K ltac:(lia) ltac:(lia)).
    replace (c <? K) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite hpc1, (wadd_id (Image1.coreAddr + (off + 4)) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

Lemma li1_blt_t s off K c imm target :
  CodeLoaded1 s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt1 off) = Iaddi 28 0 K ->
  decode (wordAt1 (off + 4)) = Iblt 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  c < K ->
  wadd (Image1.coreAddr + (off + 4)) imm = target ->
  runUntil 0 2 s = setPc (rset s 28 K) target.
Proof.
  intros hc ho hb hpc h7 hli hblt hK hc63 hlt htgt.
  rewrite coreBytes1_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length Image1.coreBytes)) by (rewrite coreBytes1_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 7 ltac:(lia) ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)); reflexivity).
  assert (hu2 : step s1 = setPc s1 target).
  { rewrite (step1_blt s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hblt), h7s1, h28s1.
    rewrite (sltb_small c K ltac:(lia) ltac:(lia)).
    replace (c <? K) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite hpc1, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

Lemma li1_bge_nt s off K c imm :
  CodeLoaded1 s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt1 off) = Iaddi 28 0 K ->
  decode (wordAt1 (off + 4)) = Ibge 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  c < K ->
  runUntil 0 2 s = setPc (rset s 28 K) (Image1.coreAddr + (off + 8)).
Proof.
  intros hc ho hb hpc h7 hli hbge hK hc63 hlt.
  rewrite coreBytes1_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length Image1.coreBytes)) by (rewrite coreBytes1_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 7 ltac:(lia) ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)); reflexivity).
  assert (hu2 : step s1 = setPc s1 (Image1.coreAddr + (off + 8))).
  { rewrite (step1_bge s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hbge), h7s1, h28s1.
    rewrite (sltb_small c K ltac:(lia) ltac:(lia)).
    replace (c <? K) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite hpc1, (wadd_id (Image1.coreAddr + (off + 4)) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

Lemma li1_bge_t s off K c imm target :
  CodeLoaded1 s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt1 off) = Iaddi 28 0 K ->
  decode (wordAt1 (off + 4)) = Ibge 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  ~ c < K ->
  wadd (Image1.coreAddr + (off + 4)) imm = target ->
  runUntil 0 2 s = setPc (rset s 28 K) target.
Proof.
  intros hc ho hb hpc h7 hli hbge hK hc63 hge htgt.
  rewrite coreBytes1_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length Image1.coreBytes)) by (rewrite coreBytes1_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 7 ltac:(lia) ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)); reflexivity).
  assert (hu2 : step s1 = setPc s1 target).
  { rewrite (step1_bge s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hbge), h7s1, h28s1.
    rewrite (sltb_small c K ltac:(lia) ltac:(lia)).
    replace (c <? K) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite hpc1, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

(** ** Well-formedness: the four regions, in address order
    code [coreAddr,+724) < input [inputAddr,+len) <= out [outAddr,+cap)
    <= lbl [lblAddr,+2048), with everything below 2^63 (signed compares on
    table addresses; label positions sign-tested in slots). *)

Record WellFormed1 (inp : list Z) (cap : Z) : Prop := {
  cap_nonneg : 0 <= cap;
  in_fits1   : Image1.inputAddr + Z.of_nat (length inp) <= Image1.outAddr;
  out_fits1  : Image1.outAddr + cap <= Image1.lblAddr;
  lbl_fits1  : Image1.lblAddr + 2048 < 2 ^ 63;
  bytes_ok1  : forall b, In b inp -> 0 <= b < 256
}.

(* cap sits below 2^63 (the out region is below the lbl region) *)
Lemma WellFormed1_cap63 inp cap : WellFormed1 inp cap -> cap < 2 ^ 63.
Proof.
  intros [Hc H1 H2 H3 H4]. unfold Image1.outAddr, Image1.lblAddr in *. lia.
Qed.

(** ** The label table encoding: undefined slot = all-ones (-1 as i64),
    defined slot = the position (< 2^63, so the sign distinguishes them). *)

Definition encodeSlot (o : option nat) : Z :=
  match o with
  | None => 2 ^ 64 - 1
  | Some p => Z.of_nat p
  end.

(* the table region holds [lab]: slot c at lblAddr + 8c, little-endian *)
Definition TableLoaded (s : State) (lab : Labels) : Prop :=
  forall c, (c < 256)%nat -> forall k, 0 <= k < 8 ->
    s.(mem) (Image1.lblAddr + 8 * Z.of_nat c + k)
      = (encodeSlot (lab c) / 2 ^ (8 * k)) mod 256.

Lemma encodeSlot_range : forall o,
  (forall p, o = Some p -> Z.of_nat p < 2 ^ 63) ->
  0 <= encodeSlot o < 2 ^ 64.
Proof.
  intros o hb. destruct o as [p|]; cbn.
  - pose proof (hb p eq_refl). lia.
  - lia.
Qed.

(* the sign test [bge slot,x0]: an undefined slot is negative ... *)
Lemma encodeSlot_none_neg : sltb (encodeSlot None) 0 = true.
Proof. reflexivity. Qed.

(* ... and a defined slot (position < 2^63) is non-negative. *)
Lemma encodeSlot_some_nonneg p : Z.of_nat p < 2 ^ 63 ->
  sltb (encodeSlot (Some p)) 0 = false.
Proof.
  intros hp. cbn.
  rewrite (sltb_small (Z.of_nat p) 0 ltac:(lia) ltac:(lia)).
  apply Z.ltb_ge. lia.
Qed.

(** ** Slot addressing and table access. *)

(* slli t3,t2,3 on a byte value: the slot offset 8c *)
Lemma wshl3 c : 0 <= c < 256 -> wshl c 3 = 8 * c.
Proof.
  intros hc. unfold wshl. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite wrap_small; change (2 ^ 3) with 8; lia.
Qed.

(* ld t4,0(t3) at slot c reads the encoded slot *)
Lemma loadWord_slot s lab c :
  TableLoaded s lab -> (c < 256)%nat ->
  0 <= encodeSlot (lab c) < 2 ^ 64 ->
  loadWord s (Image1.lblAddr + 8 * Z.of_nat c) = encodeSlot (lab c).
Proof.
  intros ht hc hv. unfold loadWord.
  pose proof (ht c hc 0 ltac:(lia)) as T0.
  pose proof (ht c hc 1 ltac:(lia)) as T1.
  pose proof (ht c hc 2 ltac:(lia)) as T2.
  pose proof (ht c hc 3 ltac:(lia)) as T3.
  pose proof (ht c hc 4 ltac:(lia)) as T4.
  pose proof (ht c hc 5 ltac:(lia)) as T5.
  pose proof (ht c hc 6 ltac:(lia)) as T6.
  pose proof (ht c hc 7 ltac:(lia)) as T7.
  replace (Image1.lblAddr + 8 * Z.of_nat c + 0)
    with (Image1.lblAddr + 8 * Z.of_nat c) in T0 by lia.
  rewrite T0, T1, T2, T3, T4, T5, T6, T7.
  change (8 * 0) with 0. change (8 * 1) with 8. change (8 * 2) with 16.
  change (8 * 3) with 24. change (8 * 4) with 32. change (8 * 5) with 40.
  change (8 * 6) with 48. change (8 * 7) with 56.
  rewrite Z.pow_0_r, Z.div_1_r.
  apply digits8. exact hv.
Qed.

(* sd t1,0(t3) at slot c installs [setLabel lab c pos] *)
Lemma storeWord_slot s lab c pos :
  TableLoaded s lab -> (c < 256)%nat ->
  TableLoaded (storeWord s (Image1.lblAddr + 8 * Z.of_nat c) (Z.of_nat pos))
              (setLabel lab c pos).
Proof.
  intros ht hc c' hc' k hk.
  unfold setLabel.
  destruct (Nat.eqb_spec c' c) as [->|hne].
  - (* the written slot: read back the stored bytes *)
    replace (Image1.lblAddr + 8 * Z.of_nat c + k)
      with ((Image1.lblAddr + 8 * Z.of_nat c) + k) by lia.
    rewrite (storeWord_get _ _ _ k hk). reflexivity.
  - (* another slot: untouched (the 8 written bytes are in slot c) *)
    rewrite storeWord_frame.
    + exact (ht c' hc' k hk).
    + intros k' hk' heq.
      assert (Z.of_nat c' <> Z.of_nat c) by lia.
      lia.
Qed.

(* a byte store OUTSIDE the table region preserves TableLoaded *)
Lemma tableLoaded_storeByte s lab a b :
  TableLoaded s lab ->
  (a < Image1.lblAddr \/ Image1.lblAddr + 2048 <= a) ->
  TableLoaded (storeByte s a b) lab.
Proof.
  intros ht hout c hc k hk.
  rewrite storeByte_mem. cbv beta.
  replace (Image1.lblAddr + 8 * Z.of_nat c + k =? a) with false
    by (symmetry; apply Z.eqb_neq; lia).
  exact (ht c hc k hk).
Qed.

(* memory-equality transport (setPc/rset chains) *)
Lemma tableLoaded_eqmem s t lab :
  t.(mem) = s.(mem) -> TableLoaded s lab -> TableLoaded t lab.
Proof. intros He H c hc k hk. rewrite He. exact (H c hc k hk). Qed.

(** ** Region predicates and their preservation lemmas. *)

Definition InputLoaded (s : State) (inp : list Z) : Prop :=
  forall j, 0 <= j < Z.of_nat (length inp) ->
    s.(mem) (Image1.inputAddr + j) = nth (Z.to_nat j) inp 0.

Lemma inputLoaded_eqmem s t inp :
  t.(mem) = s.(mem) -> InputLoaded s inp -> InputLoaded t inp.
Proof. intros He H j Hj. rewrite He. exact (H j Hj). Qed.

(* byte stores outside the code / input regions preserve them *)
Lemma codeLoaded1_storeByte s a b :
  CodeLoaded1 s ->
  (a < Image1.coreAddr \/ Image1.coreAddr + 724 <= a) ->
  CodeLoaded1 (storeByte s a b).
Proof.
  intros hc hout i hi. rewrite coreBytes1_len in hi.
  rewrite storeByte_mem. cbv beta.
  replace (Image1.coreAddr + i =? a) with false
    by (symmetry; apply Z.eqb_neq; lia).
  apply hc. rewrite coreBytes1_len. exact hi.
Qed.

Lemma inputLoaded_storeByte s a b inp :
  InputLoaded s inp ->
  (a < Image1.inputAddr \/ Image1.inputAddr + Z.of_nat (length inp) <= a) ->
  InputLoaded (storeByte s a b) inp.
Proof.
  intros hin hout j hj.
  rewrite storeByte_mem. cbv beta.
  replace (Image1.inputAddr + j =? a) with false
    by (symmetry; apply Z.eqb_neq; lia).
  exact (hin j hj).
Qed.

(* word stores outside the code / input regions preserve them *)
Lemma codeLoaded1_storeWord s a v :
  CodeLoaded1 s ->
  (a + 8 <= Image1.coreAddr \/ Image1.coreAddr + 724 <= a) ->
  CodeLoaded1 (storeWord s a v).
Proof.
  intros hc hout i hi. rewrite coreBytes1_len in hi.
  rewrite storeWord_frame by (intros k hk; lia).
  apply hc. rewrite coreBytes1_len. exact hi.
Qed.

Lemma inputLoaded_storeWord s a v inp :
  InputLoaded s inp ->
  (a + 8 <= Image1.inputAddr \/ Image1.inputAddr + Z.of_nat (length inp) <= a) ->
  InputLoaded (storeWord s a v) inp.
Proof.
  intros hin hout j hj.
  rewrite storeWord_frame by (intros k hk; lia).
  exact (hin j hj).
Qed.

(* a word store inside the table region also preserves code/input (the
   regions are in address order; geometry from WellFormed1) *)
