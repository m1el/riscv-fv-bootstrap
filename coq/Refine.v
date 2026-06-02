(** * General refinement (T1) in Coq -- mirror of lean/Hex0/Refine.lean.

    Proof-grade theorem: for ALL inputs, the real `core` computes `coreSpec`.
    No vm_compute on the general statement -- it is genuine induction.

    STATUS: `core_refines` is PROVED modulo the single per-token dispatch lemma
    `loop_iteration` (the only `Admitted`).  Everything that assembles it is
    kernel-checked, mirroring `lean/Hex0/Refine.lean` §5:
      - `fetch_code` + all 12 `step_*` lemmas + state/storeByte projections
        (`decode (wordAt off)` reduces under `vm_compute` at concrete offsets, so
        the step lemmas apply exactly as in Lean);
      - arithmetic toolkit: `wrap_small`, `wadd_id`, `toS_small`, `sltb_small`;
      - `runUntil` composition: `runUntil_halt`, `runUntil_one`, `runUntil_S`,
        `runUntil_add`, `runUntil_stab` (large-fuel halt absorption);
      - spec-side token decomposition: `decodeS_spacing`/`byte`/`comment`;
      - `core_eof` -- the EOF base case (4-step run to a correct halt);
      - `LoopInv` (the 18-field invariant) + `eof_result`;
      - `loop_correct` -- the induction (fuel bound `50*|rest| + 4`);
      - `init_loopinv` -- the prologue (2-step run to the loop head);
      - `core_refines` -- prologue + induction + `runOn<->coreSpec` conversion.
    Remaining frontier (`Admitted`, line ~425): `loop_iteration` -- the per-token
    dispatch (spacing/byte/comment + the four halting error classes), the large
    mechanical tail (~2500 Lean lines).  `Print Assumptions core_refines` =>
    `loop_iteration` + `functional_extensionality_dep` (a standard, consistent
    axiom, used for `mem : Z -> Z` state equality -- cf. Lean's propext/choice).
    Two Coq-specific notes vs Lean (see PROOF.md §8): (1) `runOn` uses a *fixed*
    fuel (100000), so the assembly bounds the step count (Lean used ∃fuel) and
    absorbs the slack via `runUntil_stab` -- note `lia` cannot reason about the
    nat literal `100000` (it is `Nat.of_num_uint`), so the bound `F <= 100000`
    is proved through `Z` (`Nat2Z.inj_le` + `vm_compute (Z.of_nat 100000)`);
    (2) the model's bytes are `Z` but the spec is on `nat`, so `LoopInv`/dispatch
    carry `Z.of_nat`/`Z.to_nat` (`zin`) conversions. *)

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

(* Once the machine has halted by fuel [f], any larger fuel [g] gives the same
   state.  Used to absorb the fixed 100000-fuel run in [runOn] into the
   step-count bound the loop actually needs (avoids nat-subtraction lia, which
   chokes on the [Nat.of_num_uint 100000] literal). *)
Lemma runUntil_stab f s : (runUntil 0 f s).(pc) = 0 ->
  forall g, (f <= g)%nat -> runUntil 0 g s = runUntil 0 f s.
Proof.
  intros Hhalt g Hle. induction Hle as [|g Hle IH].
  - reflexivity.
  - rewrite <- Nat.add_1_r, (runUntil_add g 1 s), IH.
    exact (runUntil_halt 1 (runUntil 0 f s) Hhalt).
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

(** ** Helpers for the EOF base case. *)

Lemma decodeS_nil : decodeS High [] = ([], Ok). Proof. now simp decodeS. Qed.

Lemma readMem_eq : forall l m base,
  (forall j, (j < length l)%nat -> m (base + Z.of_nat j) = Z.of_nat (nth j l 0%nat)) ->
  readMem m base (length l) = l.
Proof.
  induction l as [|a l' IH]; intros m base H; simpl; [reflexivity|].
  f_equal.
  - specialize (H 0%nat ltac:(simpl; lia)).
    replace (base + Z.of_nat 0) with base in H by lia. simpl in H. rewrite H. apply Nat2Z.id.
  - apply IH. intros j Hj. specialize (H (S j) ltac:(simpl; lia)). simpl in H.
    rewrite <- H. f_equal. lia.
Qed.

(** ** Loop invariant + the induction backbone (mirror of LoopInv/loop_correct).

    Per the fuel-bound approach: each iteration runs <= 50 instructions per input
    char consumed, so the whole loop halts within [50 * |rest| + 4] steps -- a
    closed (non-existential) bound, so it composes with the fixed-fuel `runOn`. *)

Record LoopInv (inp : list Z) (cap : Z) (s : State) (rest : list Z) (emitted : list nat) : Prop := {
  li_at_loop : s.(pc) = coreAddr + 8;
  li_code    : CodeLoaded s;
  li_a0      : rget s 10 = inputAddr;
  li_a1      : rget s 11 = Z.of_nat (length inp);
  li_a2      : rget s 12 = outAddr;
  li_a3      : rget s 13 = cap;
  li_ra      : rget s 1 = 0;
  li_in_mem  : forall j, 0 <= j < Z.of_nat (length inp) ->
                 s.(mem) (inputAddr + j) = nth (Z.to_nat j) inp 0;
  li_in_lt   : inputAddr + Z.of_nat (length inp) < 2 ^ 64;
  li_bytes   : forall b, In b inp -> 0 <= b < 256;
  li_in_fits : inputAddr + Z.of_nat (length inp) <= outAddr;
  li_out_lt  : outAddr + cap < 2 ^ 64;
  li_idx     : rget s 5 = Z.of_nat (length inp) - Z.of_nat (length rest);
  li_suffix  : skipn (length inp - length rest) inp = rest;
  li_outidx  : rget s 6 = Z.of_nat (length emitted);
  li_emit_le : (length emitted <= Z.to_nat cap)%nat;
  li_out_mem : forall j, (j < length emitted)%nat ->
                 s.(mem) (outAddr + Z.of_nat j) = Z.of_nat (nth j emitted 0%nat);
  li_spec    : decodeS High (zin inp) =
                 (emitted ++ fst (decodeS High (zin rest)), snd (decodeS High (zin rest)))
}.

(* The halted observation matches coreSpec. *)
Definition Result (f : State) (inp : list Z) (cap : Z) : Prop :=
  let '(st, bs, ln) := coreSpec (zin inp) (Z.to_nat cap) in
  f.(pc) = 0 /\ rget f 10 = Z.of_nat st /\ rget f 11 = Z.of_nat ln /\
  readMem f.(mem) outAddr ln = bs.

Lemma Result_pc f inp cap : Result f inp cap -> f.(pc) = 0.
Proof. unfold Result. destruct (coreSpec (zin inp) (Z.to_nat cap)) as [[st bs] ln]. tauto. Qed.

(* Base case: input exhausted -> halts Ok with output preserved. (Uses core_eof;
   the readMem/coreSpec packaging is the remaining detail -- Admitted for now.) *)
Theorem eof_result : forall inp cap emitted s,
  LoopInv inp cap s [] emitted -> Result (runUntil 0 4 s) inp cap.
Proof.
  intros inp cap emitted s HI.
  destruct HI as [Hpc Hcode Ha0 Ha1 Ha2 Ha3 Hra Hinmem Hinlt Hbytes Hinfits Houtlt
                  Hidx Hsuf Houtidx Hemitle Houtmem Hspec].
  assert (h5 : rget s 5 = Z.of_nat (length inp)) by (rewrite Hidx; simpl length; lia).
  assert (hE : 0 <= Z.of_nat (length emitted) < 2 ^ 64) by (unfold outAddr in Houtlt; lia).
  destruct (core_eof s (Z.of_nat (length inp)) (Z.of_nat (length emitted))
              Hcode Hpc h5 Ha1 Houtidx Hra hE) as [Hp [H10 [H11 Hmem]]].
  (* coreSpec computes to (0, emitted, length emitted) *)
  assert (Hdec : Spec.decode (zin inp) = (emitted, Ok)).
  { unfold Spec.decode. rewrite Hspec. change (zin []) with (@nil nat).
    rewrite decodeS_nil. simpl. rewrite app_nil_r. reflexivity. }
  assert (Hcs : coreSpec (zin inp) (Z.to_nat cap) = (0%nat, emitted, length emitted)).
  { unfold coreSpec. rewrite Hdec.
    destruct (Z.to_nat cap <? length emitted)%nat eqn:Ecap.
    - apply Nat.ltb_lt in Ecap. lia.
    - reflexivity. }
  unfold Result. rewrite Hcs. repeat split.
  - exact Hp.
  - rewrite H10. reflexivity.
  - rewrite H11. reflexivity.
  - rewrite Hmem. apply readMem_eq. intros j Hj. exact (Houtmem j Hj).
Qed.

(** ** Reusable machine-stepping blocks (mirror of lean/Hex0/Refine.lean's
    "reusable blocks").  Ported bottom-up; each is consumed by the per-token
    [loop_*] cases that build [loop_iteration]. *)

(* [li t3,K; beq t2,t3,_] where t2 = c <> K: runs as 2 steps, the beq falling
   through (not taken) to off+8.  Clobbers only t3 (=x28) and pc.  Mirror of the
   Lean [li_beq_ne].  (t2 = x7, t3 = x28.) *)
Lemma li_beq_ne s off K c imm :
  CodeLoaded s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt off) = Iaddi 28 0 K ->
  decode (wordAt (off + 4)) = Ibeq 7 28 imm ->
  0 <= K < 2 ^ 64 ->
  c <> K ->
  runUntil 0 2 s = setPc (rset s 28 K) (coreAddr + (off + 8)).
Proof.
  intros hc ho hb hpc h7 hli hbeq hK hne.
  rewrite coreBytes_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length coreBytes)) by (rewrite coreBytes_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1)
    by (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget; exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget; reflexivity).
  assert (hu2 : step s1 = setPc s1 (coreAddr + (off + 8))).
  { rewrite (step_beq s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes_len; lia) hpc1 hbeq), h7s1, h28s1.
    replace (c =? K) with false by (symmetry; apply Z.eqb_neq; exact hne).
    rewrite hpc1, (wadd_id (coreAddr + (off + 4)) 4 ltac:(unfold coreAddr; lia)).
    f_equal. lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

(* [li t3,K; beq t2,t3,_] where t2 = c = K: 2 steps, the beq TAKEN to [target]
   (= pc+imm).  Clobbers only t3/pc.  Mirror of Lean [li_beq_eq]. *)
Lemma li_beq_eq s off K c imm target :
  CodeLoaded s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt off) = Iaddi 28 0 K ->
  decode (wordAt (off + 4)) = Ibeq 7 28 imm ->
  0 <= K < 2 ^ 64 ->
  c = K ->
  wadd (coreAddr + (off + 4)) imm = target ->
  runUntil 0 2 s = setPc (rset s 28 K) target.
Proof.
  intros hc ho hb hpc h7 hli hbeq hK heq htgt.
  rewrite coreBytes_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length coreBytes)) by (rewrite coreBytes_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1)
    by (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget; exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget; reflexivity).
  assert (hu2 : step s1 = setPc s1 target).
  { rewrite (step_beq s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes_len; lia) hpc1 hbeq), h7s1, h28s1.
    replace (c =? K) with true by (symmetry; apply Z.eqb_eq; exact heq).
    rewrite hpc1, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

(* Frame: a [(rset s 28 v).setPc P] state inherits every register != t3 from s. *)
Lemma li_block_frame s v P i : i <> 28 ->
  rget (setPc (rset s 28 v) P) i = rget s i.
Proof.
  intros hi. rewrite setPc_rget. destruct (i =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. subst i. reflexivity.
  - apply Z.eqb_neq in E0.
    rewrite (rset_rget s 28 v i ltac:(lia) E0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact hi).
    reflexivity.
Qed.

(* The shared input-read head (offsets 8..24): from the loop head with a
   non-empty suffix [c :: rest'], 4 steps read the head char [c] into [t2] and
   bump [t0].  Lands at offset 24 (the spacing beq-chain).  Mirror of Lean
   [loop_prefix]. *)
Lemma loop_prefix : forall inp cap c rest' emitted s,
  LoopInv inp cap s (c :: rest') emitted ->
  (runUntil 0 4 s).(pc) = coreAddr + 24 /\
  rget (runUntil 0 4 s) 7 = c /\
  rget (runUntil 0 4 s) 5 = rget s 5 + 1 /\
  (runUntil 0 4 s).(mem) = s.(mem) /\
  CodeLoaded (runUntil 0 4 s) /\
  (forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 ->
     rget (runUntil 0 4 s) i = rget s i).
Proof.
  intros inp cap c rest' emitted s HI.
  destruct HI as [Hpc Hcode Ha0 Ha1 Ha2 Ha3 Hra Hinmem Hinlt Hbytes Hinfits Houtlt
                  Hidx Hsuf Houtidx Hemitle Houtmem Hspec].
  set (k := (length inp - length (c :: rest'))%nat) in *.
  set (jZ := Z.of_nat (length inp) - Z.of_nat (length (c :: rest'))) in *.
  assert (hlen1 : Z.of_nat (length (c :: rest')) = Z.of_nat (length rest') + 1)
    by (simpl length; lia).
  assert (hge : (length (c :: rest') <= length inp)%nat).
  { pose proof (f_equal (@length Z) Hsuf) as Hl. rewrite length_skipn in Hl.
    fold k in Hl. lia. }
  assert (htonat : Z.to_nat jZ = k).
  { unfold jZ, k. rewrite <- Nat2Z.inj_sub by lia. rewrite Nat2Z.id. reflexivity. }
  assert (hjpos : 0 <= jZ) by (unfold jZ; lia).
  assert (hjlt : jZ < Z.of_nat (length inp)) by (unfold jZ; lia).
  assert (Hc : nth k inp 0 = c).
  { transitivity (nth 0 (skipn k inp) 0).
    - rewrite nth_skipn. f_equal. lia.
    - rewrite Hsuf. reflexivity. }
  assert (Hin : In c inp).
  { rewrite <- (firstn_skipn k inp). apply in_or_app. right.
    fold k in Hsuf. rewrite Hsuf. left; reflexivity. }
  assert (Hcr : 0 <= c < 256) by (apply Hbytes; exact Hin).
  (* step 1: bgeu t0,a1 NOT taken (idx < len) -> off 12 *)
  assert (hult : ultb (rget s 5) (rget s 11) = true).
  { rewrite Hidx, Ha1. unfold ultb. apply Z.ltb_lt. exact hjlt. }
  assert (hs1 : step s = setPc s (coreAddr + 12)).
  { rewrite (step_bgeu s 8 5 11 256 Hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) Hpc
              ltac:(vm_compute; reflexivity)), hult. cbn match.
    rewrite Hpc, (wadd_id (coreAddr + 8) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s1 := setPc s (coreAddr + 12)) in *.
  assert (hc1 : CodeLoaded s1)
    by (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem; reflexivity| exact Hcode]).
  assert (hpc1 : s1.(pc) = coreAddr + 12) by reflexivity.
  (* step 2: add t3,a0,t0  (t3 = inputAddr + idx) -> off 16 *)
  assert (haddr : wadd (rget s1 10) (rget s1 5) = inputAddr + jZ).
  { unfold s1. rewrite !setPc_rget, Ha0, Hidx. apply wadd_id. unfold inputAddr in *; lia. }
  assert (hs2 : step s1 = setPc (rset s1 28 (inputAddr + jZ)) (coreAddr + 16)).
  { rewrite (step_add s1 12 28 10 5 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1
              ltac:(vm_compute; reflexivity)), haddr, hpc1,
            (wadd_id (coreAddr + 12) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s2 := setPc (rset s1 28 (inputAddr + jZ)) (coreAddr + 16)) in *.
  assert (hmem2 : s2.(mem) = s.(mem))
    by (unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem; reflexivity).
  assert (hc2 : CodeLoaded s2) by (apply (CodeLoaded_eqmem s); [exact hmem2| exact Hcode]).
  assert (hpc2 : s2.(pc) = coreAddr + 16) by reflexivity.
  (* step 3: lbu t2,0(t3)  (t2 = input byte c) -> off 20 *)
  assert (hr28_2 : rget s2 28 = inputAddr + jZ).
  { unfold s2. rewrite setPc_rget, (rset_rget s1 28 (inputAddr + jZ) 28 ltac:(lia) ltac:(lia)),
            Z.eqb_refl. reflexivity. }
  assert (hbyte : s2.(mem) (wadd (rget s2 28) 0) mod 256 = c).
  { rewrite hr28_2, (wadd_id (inputAddr + jZ) 0 ltac:(unfold inputAddr in *; lia)), Z.add_0_r,
            hmem2, (Hinmem jZ ltac:(lia)), htonat, Hc. apply Z.mod_small. exact Hcr. }
  assert (hs3 : step s2 = setPc (rset s2 7 c) (coreAddr + 20)).
  { rewrite (step_lbu s2 16 7 28 0 hc2 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc2
              ltac:(vm_compute; reflexivity)), hbyte, hpc2,
            (wadd_id (coreAddr + 16) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s3 := setPc (rset s2 7 c) (coreAddr + 20)) in *.
  assert (hmem3 : s3.(mem) = s.(mem))
    by (unfold s3; rewrite setPc_mem, rset_mem; exact hmem2).
  assert (hc3 : CodeLoaded s3) by (apply (CodeLoaded_eqmem s); [exact hmem3| exact Hcode]).
  assert (hpc3 : s3.(pc) = coreAddr + 20) by reflexivity.
  (* step 4: addi t0,t0,1  (bump index) -> off 24 *)
  assert (hr5_3 : rget s3 5 = jZ).
  { unfold s3. rewrite setPc_rget, (rset_rget s2 7 c 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 7) with false by reflexivity.
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 (inputAddr + jZ) 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 28) with false by reflexivity.
    unfold s1. rewrite setPc_rget. exact Hidx. }
  assert (hs4 : step s3 = setPc (rset s3 5 (jZ + 1)) (coreAddr + 24)).
  { rewrite (step_addi s3 20 5 5 1 hc3 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc3
              ltac:(vm_compute; reflexivity)), hr5_3,
            (wadd_id jZ 1 ltac:(unfold inputAddr in *; lia)), hpc3,
            (wadd_id (coreAddr + 20) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s4 := setPc (rset s3 5 (jZ + 1)) (coreAddr + 24)) in *.
  assert (hmem4 : s4.(mem) = s.(mem))
    by (unfold s4; rewrite setPc_mem, rset_mem; exact hmem3).
  (* assemble runUntil 0 4 s = s4 *)
  assert (hp0 : s.(pc) <> 0) by (rewrite Hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; apply coreAddr_pos; lia).
  assert (hp3 : s3.(pc) <> 0) by (rewrite hpc3; apply coreAddr_pos; lia).
  assert (hrun : runUntil 0 4 s = s4).
  { rewrite (runUntil_S 3 s hp0), hs1, (runUntil_S 2 s1 hp1), hs2,
            (runUntil_S 1 s2 hp2), hs3, (runUntil_S 0 s3 hp3), hs4. reflexivity. }
  rewrite hrun. repeat apply conj.
  - unfold s4. apply setPc_pc.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 5 (jZ + 1) 7 ltac:(lia) ltac:(lia)).
    replace (7 =? 5) with false by reflexivity.
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 c 7 ltac:(lia) ltac:(lia)), Z.eqb_refl.
    reflexivity.
  - assert (H54 : rget s4 5 = jZ + 1) by
      (unfold s4; rewrite setPc_rget, (rset_rget s3 5 (jZ + 1) 5 ltac:(lia) ltac:(lia)),
            Z.eqb_refl; reflexivity).
    lia.
  - exact hmem4.
  - apply (CodeLoaded_eqmem s); [exact hmem4| exact Hcode].
  - intros i h0 h5 h7 h28.
    unfold s4. rewrite setPc_rget, (rset_rget s3 5 (jZ + 1) i ltac:(lia) h0).
    replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 c i ltac:(lia) h0).
    replace (i =? 7) with false by (symmetry; apply Z.eqb_neq; exact h7).
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 (inputAddr + jZ) i ltac:(lia) h0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
    unfold s1. rewrite setPc_rget. reflexivity.
Qed.

(* The three spacing characters, as Z (mirror of the [isSpace] disjunction). *)
Lemma isSpace_cases c : 0 <= c -> isSpace (Z.to_nat c) = true ->
  c = 10 \/ c = 32 \/ c = 95.
Proof.
  intros h0 hs. unfold isSpace, c_nl, c_sp, c_us in hs.
  rewrite !orb_true_iff, !Nat.eqb_eq in hs.
  assert (Hid : c = Z.of_nat (Z.to_nat c)) by (rewrite Z2Nat.id; [reflexivity| exact h0]).
  destruct hs as [[H|H]|H]; [left|right; left|right; right]; rewrite Hid, H; reflexivity.
Qed.

(* The head char of a non-empty suffix is an input byte. *)
Lemma loopinv_head inp cap c rest' emitted s :
  LoopInv inp cap s (c :: rest') emitted -> In c inp /\ 0 <= c < 256.
Proof.
  intros HI. destruct HI as [_ _ _ _ _ _ _ _ _ Hbytes _ _ _ Hsuf _ _ _ _].
  assert (Hin : In c inp).
  { rewrite <- (firstn_skipn (length inp - length (c :: rest')) inp).
    apply in_or_app. right. rewrite Hsuf. left; reflexivity. }
  split; [exact Hin| apply Hbytes; exact Hin].
Qed.

(* The spacing beq-chain (offsets 24..): from [s4] at off 24 with [t2 = c] a
   spacing char, some number of steps reach LOOP, touching only [t3].  Mirror of
   Lean [spacing_tail]. *)
Lemma spacing_tail s4 c :
  CodeLoaded s4 -> s4.(pc) = coreAddr + 24 -> rget s4 7 = c ->
  0 <= c -> isSpace (Z.to_nat c) = true ->
  exists k, (runUntil 0 k s4).(pc) = coreAddr + 8 /\
            (runUntil 0 k s4).(mem) = s4.(mem) /\
            (forall i, i <> 28 -> rget (runUntil 0 k s4) i = rget s4 i).
Proof.
  intros hcode hpc ht2 h0 hss.
  destruct (isSpace_cases c h0 hss) as [hc|[hc|hc]].
  all: assert (hne35 : c <> 35) by lia.
  all: assert (hne59 : c <> 59) by lia.
  (* block at off 24 (K=35), not taken *)
  all: pose proof (li_beq_ne s4 24 35 c 208 hcode ltac:(lia)
         ltac:(rewrite coreBytes_len; lia) hpc ht2 ltac:(vm_compute; reflexivity)
         ltac:(vm_compute; reflexivity) ltac:(lia) hne35) as hb1.
  all: set (s_b := setPc (rset s4 28 35) (coreAddr + (24 + 8))) in *.
  all: assert (hcb : CodeLoaded s_b) by
         (apply (CodeLoaded_eqmem s4); [unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  all: assert (hpcb : s_b.(pc) = coreAddr + 32) by (unfold s_b; reflexivity).
  all: assert (h7b : rget s_b 7 = c) by
         (unfold s_b; rewrite (li_block_frame s4 35 (coreAddr + (24 + 8)) 7 ltac:(lia)); exact ht2).
  (* block at off 32 (K=59), not taken *)
  all: pose proof (li_beq_ne s_b 32 59 c 200 hcb ltac:(lia)
         ltac:(rewrite coreBytes_len; lia) hpcb h7b ltac:(vm_compute; reflexivity)
         ltac:(vm_compute; reflexivity) ltac:(lia) hne59) as hb2.
  all: set (s_c := setPc (rset s_b 28 59) (coreAddr + (32 + 8))) in *.
  all: assert (hcc : CodeLoaded s_c) by
         (apply (CodeLoaded_eqmem s4); [unfold s_c; rewrite setPc_mem, rset_mem;
            unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  all: assert (hpcc : s_c.(pc) = coreAddr + 40) by (unfold s_c; reflexivity).
  all: assert (h7c : rget s_c 7 = c) by
         (unfold s_c; rewrite (li_block_frame s_b 59 (coreAddr + (32 + 8)) 7 ltac:(lia)); exact h7b).
  - (* c = 10: taken at off 40 *)
    pose proof (li_beq_eq s_c 40 10 c (-36) (coreAddr + 8) hcc ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpcc h7c ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) hc
      ltac:(rewrite (wadd_id (coreAddr + (40 + 4)) (-36) ltac:(unfold coreAddr; lia)); lia)) as hb3.
    assert (hfin : runUntil 0 (2 + (2 + 2)) s4 = setPc (rset s_c 28 10) (coreAddr + 8))
      by (rewrite runUntil_add, hb1, runUntil_add, hb2, hb3; reflexivity).
    exists (2 + (2 + 2))%nat. rewrite hfin. repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_c. rewrite setPc_mem, rset_mem.
      unfold s_b. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame s_c 10 (coreAddr + 8) i hi).
      unfold s_c. rewrite (li_block_frame s_b 59 (coreAddr + (32 + 8)) i hi).
      unfold s_b. rewrite (li_block_frame s4 35 (coreAddr + (24 + 8)) i hi). reflexivity.
  - (* c = 32: not taken at 40, taken at 48 *)
    pose proof (li_beq_ne s_c 40 10 c (-36) hcc ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpcc h7c ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
    set (s_d := setPc (rset s_c 28 10) (coreAddr + (40 + 8))) in *.
    assert (hcd : CodeLoaded s_d) by
      (apply (CodeLoaded_eqmem s4); [unfold s_d; rewrite setPc_mem, rset_mem;
         unfold s_c; rewrite setPc_mem, rset_mem; unfold s_b; rewrite setPc_mem, rset_mem;
         reflexivity| exact hcode]).
    assert (hpcd : s_d.(pc) = coreAddr + 48) by (unfold s_d; reflexivity).
    assert (h7d : rget s_d 7 = c) by
      (unfold s_d; rewrite (li_block_frame s_c 10 (coreAddr + (40 + 8)) 7 ltac:(lia)); exact h7c).
    pose proof (li_beq_eq s_d 48 32 c (-44) (coreAddr + 8) hcd ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpcd h7d ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) hc
      ltac:(rewrite (wadd_id (coreAddr + (48 + 4)) (-44) ltac:(unfold coreAddr; lia)); lia)) as hb4.
    assert (hfin : runUntil 0 (2 + (2 + (2 + 2))) s4 = setPc (rset s_d 28 32) (coreAddr + 8))
      by (rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, hb4; reflexivity).
    exists (2 + (2 + (2 + 2)))%nat. rewrite hfin. repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_d. rewrite setPc_mem, rset_mem.
      unfold s_c. rewrite setPc_mem, rset_mem. unfold s_b. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame s_d 32 (coreAddr + 8) i hi).
      unfold s_d. rewrite (li_block_frame s_c 10 (coreAddr + (40 + 8)) i hi).
      unfold s_c. rewrite (li_block_frame s_b 59 (coreAddr + (32 + 8)) i hi).
      unfold s_b. rewrite (li_block_frame s4 35 (coreAddr + (24 + 8)) i hi). reflexivity.
  - (* c = 95: not taken at 40 and 48, taken at 56 *)
    pose proof (li_beq_ne s_c 40 10 c (-36) hcc ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpcc h7c ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
    set (s_d := setPc (rset s_c 28 10) (coreAddr + (40 + 8))) in *.
    assert (hcd : CodeLoaded s_d) by
      (apply (CodeLoaded_eqmem s4); [unfold s_d; rewrite setPc_mem, rset_mem;
         unfold s_c; rewrite setPc_mem, rset_mem; unfold s_b; rewrite setPc_mem, rset_mem;
         reflexivity| exact hcode]).
    assert (hpcd : s_d.(pc) = coreAddr + 48) by (unfold s_d; reflexivity).
    assert (h7d : rget s_d 7 = c) by
      (unfold s_d; rewrite (li_block_frame s_c 10 (coreAddr + (40 + 8)) 7 ltac:(lia)); exact h7c).
    pose proof (li_beq_ne s_d 48 32 c (-44) hcd ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpcd h7d ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
    set (s_e := setPc (rset s_d 28 32) (coreAddr + (48 + 8))) in *.
    assert (hce : CodeLoaded s_e) by
      (apply (CodeLoaded_eqmem s4); [unfold s_e; rewrite setPc_mem, rset_mem;
         unfold s_d; rewrite setPc_mem, rset_mem; unfold s_c; rewrite setPc_mem, rset_mem;
         unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpce : s_e.(pc) = coreAddr + 56) by (unfold s_e; reflexivity).
    assert (h7e : rget s_e 7 = c) by
      (unfold s_e; rewrite (li_block_frame s_d 32 (coreAddr + (48 + 8)) 7 ltac:(lia)); exact h7d).
    pose proof (li_beq_eq s_e 56 95 c (-52) (coreAddr + 8) hce ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpce h7e ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) hc
      ltac:(rewrite (wadd_id (coreAddr + (56 + 4)) (-52) ltac:(unfold coreAddr; lia)); lia)) as hb5.
    assert (hfin : runUntil 0 (2 + (2 + (2 + (2 + 2)))) s4 = setPc (rset s_e 28 95) (coreAddr + 8))
      by (rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, runUntil_add, hb4, hb5;
          reflexivity).
    exists (2 + (2 + (2 + (2 + 2))))%nat. rewrite hfin. repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_e. rewrite setPc_mem, rset_mem.
      unfold s_d. rewrite setPc_mem, rset_mem. unfold s_c. rewrite setPc_mem, rset_mem.
      unfold s_b. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame s_e 95 (coreAddr + 8) i hi).
      unfold s_e. rewrite (li_block_frame s_d 32 (coreAddr + (48 + 8)) i hi).
      unfold s_d. rewrite (li_block_frame s_c 10 (coreAddr + (40 + 8)) i hi).
      unfold s_c. rewrite (li_block_frame s_b 59 (coreAddr + (32 + 8)) i hi).
      unfold s_b. rewrite (li_block_frame s4 35 (coreAddr + (24 + 8)) i hi). reflexivity.
Qed.

(* Rebuild the loop invariant after a spacing token: same [emitted], suffix
   shortened by one, index bumped.  Mirror of Lean [spacing_loopinv]. *)
Lemma spacing_loopinv inp cap c rest' emitted s s' :
  LoopInv inp cap s (c :: rest') emitted ->
  isComment (Z.to_nat c) = false -> isSpace (Z.to_nat c) = true ->
  s'.(pc) = coreAddr + 8 -> s'.(mem) = s.(mem) ->
  rget s' 5 = rget s 5 + 1 ->
  rget s' 1 = rget s 1 -> rget s' 6 = rget s 6 ->
  rget s' 10 = rget s 10 -> rget s' 11 = rget s 11 ->
  rget s' 12 = rget s 12 -> rget s' 13 = rget s 13 ->
  LoopInv inp cap s' rest' emitted.
Proof.
  intros HI hsc hss hpc' hmem' h5 hp1 hp6 hp10 hp11 hp12 hp13.
  destruct HI as [Hpc Hcode Ha0 Ha1 Ha2 Ha3 Hra Hinmem Hinlt Hbytes Hinfits Houtlt
                  Hidx Hsuf Houtidx Hemitle Houtmem Hspec].
  assert (hlen1 : Z.of_nat (length (c :: rest')) = Z.of_nat (length rest') + 1)
    by (simpl length; lia).
  assert (hge : (length (c :: rest') <= length inp)%nat).
  { pose proof (f_equal (@length Z) Hsuf) as Hl. rewrite length_skipn in Hl. lia. }
  refine {| li_at_loop := hpc'; li_code := _; li_a0 := _; li_a1 := _; li_a2 := _;
            li_a3 := _; li_ra := _; li_in_mem := _; li_in_lt := Hinlt;
            li_bytes := Hbytes; li_in_fits := Hinfits; li_out_lt := Houtlt;
            li_idx := _; li_suffix := _; li_outidx := _; li_emit_le := Hemitle;
            li_out_mem := _; li_spec := _ |}.
  - apply (CodeLoaded_eqmem s); [exact hmem'| exact Hcode].
  - rewrite hp10; exact Ha0.
  - rewrite hp11; exact Ha1.
  - rewrite hp12; exact Ha2.
  - rewrite hp13; exact Ha3.
  - rewrite hp1; exact Hra.
  - intros j hj. rewrite hmem'. exact (Hinmem j hj).
  - rewrite h5, Hidx. lia.
  - assert (Hk1 : (length inp - length rest')%nat = S (length inp - length (c :: rest')))
      by (simpl length; lia).
    rewrite Hk1, <- Nat.add_1_l, <- (skipn_skipn 1 (length inp - length (c :: rest')) inp),
            Hsuf. reflexivity.
  - rewrite hp6; exact Houtidx.
  - intros j hj. rewrite hmem'. exact (Houtmem j hj).
  - rewrite Hspec. change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
    rewrite (decodeS_spacing (Z.to_nat c) (zin rest') hsc hss). reflexivity.
Qed.

(* A COMPLETE main-loop iteration for any spacing token: loop_prefix (read the
   char) + spacing_tail (dispatch to LOOP) + spacing_loopinv (rebuild).  Mirror
   of Lean [loop_spacing]. *)
Lemma loop_spacing inp cap c rest' emitted s :
  isSpace (Z.to_nat c) = true ->
  LoopInv inp cap s (c :: rest') emitted ->
  exists k, LoopInv inp cap (runUntil 0 k s) rest' emitted.
Proof.
  intros hss inv.
  destruct (loopinv_head inp cap c rest' emitted s inv) as [Hin [Hc0 _]].
  assert (hsc : isComment (Z.to_nat c) = false)
    by (destruct (isSpace_cases c Hc0 hss) as [H|[H|H]]; subst c; reflexivity).
  destruct (loop_prefix inp cap c rest' emitted s inv)
    as [hpc4 [ht2 [ht0 [hmem4 [hcode4 hother4]]]]].
  destruct (spacing_tail (runUntil 0 4 s) c hcode4 hpc4 ht2 Hc0 hss)
    as [k [htpc [htmem htother]]].
  exists (4 + k)%nat. rewrite runUntil_add.
  apply (spacing_loopinv inp cap c rest' emitted s (runUntil 0 k (runUntil 0 4 s)) inv hsc hss).
  - exact htpc.
  - rewrite htmem; exact hmem4.
  - rewrite (htother 5 ltac:(lia)); exact ht0.
  - rewrite (htother 1 ltac:(lia)); exact (hother4 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite (htother 6 ltac:(lia)); exact (hother4 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite (htother 10 ltac:(lia)); exact (hother4 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite (htother 11 ltac:(lia)); exact (hother4 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite (htother 12 ltac:(lia)); exact (hother4 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite (htother 13 ltac:(lia)); exact (hother4 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(** ** Error infrastructure (mirror of error_result/halt_epilogue/bgeu_eq_taken/
    reach_error).  The halting epilogue + spec packaging shared by every error
    class (and the comment-EOF Ok exit). *)

(* From a halted state with the right a0/a1/output, package a [Result] for a
   non-truncating decode.  Mirror of Lean [error_result]. *)
Lemma error_result s inp cap emitted st :
  s.(pc) = 0 -> rget s 10 = Z.of_nat (statusCode st) ->
  rget s 11 = Z.of_nat (length emitted) ->
  (forall j, (j < length emitted)%nat ->
     s.(mem) (outAddr + Z.of_nat j) = Z.of_nat (nth j emitted 0%nat)) ->
  Spec.decode (zin inp) = (emitted, st) -> (length emitted <= Z.to_nat cap)%nat ->
  Result s inp cap.
Proof.
  intros hp ha0 ha1 hmem hdec hle.
  assert (hcs : coreSpec (zin inp) (Z.to_nat cap) = (statusCode st, emitted, length emitted)).
  { unfold coreSpec. rewrite hdec. destruct (Z.to_nat cap <? length emitted)%nat eqn:E.
    - apply Nat.ltb_lt in E. lia.
    - reflexivity. }
  unfold Result. rewrite hcs. repeat apply conj.
  - exact hp.
  - exact ha0.
  - exact ha1.
  - apply readMem_eq. exact hmem.
Qed.

(* The halting epilogue (li a0,code; mv a1,t1; ret): 3 steps to pc=0 with
   a0=code, a1=t1, memory preserved.  Mirror of Lean [halt_epilogue]. *)
Lemma halt_epilogue s off code n :
  CodeLoaded s -> 0 <= off -> off + 8 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off ->
  decode (wordAt off) = Iaddi 10 0 code ->
  decode (wordAt (off + 4)) = Iaddi 11 6 0 ->
  decode (wordAt (off + 8)) = Ijalr 0 1 0 ->
  0 <= code < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  rget s 6 = n -> rget s 1 = 0 ->
  (runUntil 0 3 s).(pc) = 0 /\ rget (runUntil 0 3 s) 10 = code /\
  rget (runUntil 0 3 s) 11 = n /\ (runUntil 0 3 s).(mem) = s.(mem).
Proof.
  intros hcode ho hoff hpc hli hmv hret hcodeR hnR h6 h1.
  rewrite coreBytes_len in hoff.
  assert (hs1 : step s = setPc (rset s 10 code) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 10 0 code hcode ho ltac:(rewrite coreBytes_len; lia) hpc hli), rget_zero,
      (wadd_id 0 code ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s1 := setPc (rset s 10 code) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1) by
    (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h6_1 : rget s1 6 = n).
  { unfold s1. rewrite setPc_rget, (rset_rget s 10 code 6 ltac:(lia) ltac:(lia)).
    replace (6 =? 10) with false by reflexivity. exact h6. }
  assert (hs2 : step s1 = setPc (rset s1 11 n) (coreAddr + (off + 8))).
  { rewrite (step_addi s1 (off + 4) 11 6 0 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1 hmv), h6_1,
      (wadd_id n 0 ltac:(lia)), Z.add_0_r, hpc1,
      (wadd_id (coreAddr + (off + 4)) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s2 := setPc (rset s1 11 n) (coreAddr + (off + 8))) in *.
  assert (hc2 : CodeLoaded s2) by
    (apply (CodeLoaded_eqmem s); [unfold s2, s1; rewrite !setPc_mem, !rset_mem; reflexivity| exact hcode]).
  assert (hpc2 : s2.(pc) = coreAddr + (off + 8)) by reflexivity.
  assert (h1_2 : rget s2 1 = 0).
  { unfold s2. rewrite setPc_rget, (rset_rget s1 11 n 1 ltac:(lia) ltac:(lia)).
    replace (1 =? 11) with false by reflexivity. unfold s1.
    rewrite setPc_rget, (rset_rget s 10 code 1 ltac:(lia) ltac:(lia)).
    replace (1 =? 10) with false by reflexivity. exact h1. }
  assert (hs3 : step s2 = setPc s2 0).
  { rewrite (step_jalr s2 (off + 8) 0 1 0 hc2 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc2 hret).
    assert (Hr : rset s2 0 (wadd s2.(pc) 4) = s2) by (unfold rset; reflexivity).
    rewrite Hr, h1_2, (wadd_id 0 0 ltac:(lia)). reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; apply coreAddr_pos; lia).
  assert (hrun : runUntil 0 3 s = setPc s2 0).
  { rewrite (runUntil_S 2 s hp0), hs1, (runUntil_S 1 s1 hp1), hs2,
            (runUntil_S 0 s2 hp2), hs3. reflexivity. }
  rewrite hrun. repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_rget. unfold s2.
    rewrite setPc_rget, (rset_rget s1 11 n 10 ltac:(lia) ltac:(lia)).
    replace (10 =? 11) with false by reflexivity. unfold s1.
    rewrite setPc_rget, (rset_rget s 10 code 10 ltac:(lia) ltac:(lia)), Z.eqb_refl. reflexivity.
  - rewrite setPc_rget. unfold s2.
    rewrite setPc_rget, (rset_rget s1 11 n 11 ltac:(lia) ltac:(lia)), Z.eqb_refl. reflexivity.
  - rewrite setPc_mem. unfold s2, s1. rewrite !setPc_mem, !rset_mem. reflexivity.
Qed.

(* A [bgeu rs1,rs2] with equal operands branches (1 step to the target).  Mirror
   of Lean [bgeu_eq_taken]. *)
Lemma bgeu_eq_taken s off rs1 rs2 A immB target :
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off ->
  rget s rs1 = A -> rget s rs2 = A ->
  decode (wordAt off) = Ibgeu rs1 rs2 immB ->
  wadd (coreAddr + off) immB = target ->
  runUntil 0 1 s = setPc s target.
Proof.
  intros hcode ho hoff hpc h1 h2 hbgeu htgt.
  assert (hult : ultb (rget s rs1) (rget s rs2) = false)
    by (rewrite h1, h2; unfold ultb; apply Z.ltb_irrefl).
  assert (hu1 : step s = setPc s target).
  { rewrite (step_bgeu s off rs1 rs2 immB hcode ho hoff hpc hbgeu), hult. cbn match.
    rewrite hpc, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  rewrite (runUntil_one s hp0), hu1. reflexivity.
Qed.

(* Run from the loop head to an error label, then halt; package a [Result].
   Mirror of Lean [reach_error]. *)
Lemma reach_error s sE inp cap emitted off code k st :
  runUntil 0 k s = sE ->
  sE.(pc) = coreAddr + off -> CodeLoaded sE -> sE.(mem) = s.(mem) ->
  rget sE 6 = Z.of_nat (length emitted) -> rget sE 1 = 0 ->
  decode (wordAt off) = Iaddi 10 0 code ->
  decode (wordAt (off + 4)) = Iaddi 11 6 0 ->
  decode (wordAt (off + 8)) = Ijalr 0 1 0 ->
  0 <= off -> off + 8 + 3 < Z.of_nat (length coreBytes) ->
  0 <= code < 2 ^ 64 -> Z.of_nat (length emitted) < 2 ^ 64 ->
  code = Z.of_nat (statusCode st) ->
  Spec.decode (zin inp) = (emitted, st) -> (length emitted <= Z.to_nat cap)%nat ->
  (forall j, (j < length emitted)%nat ->
     s.(mem) (outAddr + Z.of_nat j) = Z.of_nat (nth j emitted 0%nat)) ->
  exists m, Result (runUntil 0 m s) inp cap.
Proof.
  intros hrun hpcE hcodeE hmemE h6E h1E hli hmv hret ho hoff hcodeR hemit_lt
         hcodeval hdec hle hout.
  destruct (halt_epilogue sE off code (Z.of_nat (length emitted)) hcodeE ho hoff hpcE
              hli hmv hret hcodeR ltac:(lia) h6E h1E) as [hp [ha0 [ha1 hm]]].
  exists (k + 3)%nat. rewrite runUntil_add, hrun.
  apply (error_result (runUntil 0 3 sE) inp cap emitted st).
  - exact hp.
  - rewrite ha0; exact hcodeval.
  - exact ha1.
  - intros j hj. rewrite hm, hmemE. exact (hout j hj).
  - exact hdec.
  - exact hle.
Qed.

(** ** Signed-branch [li;blt]/[li;bge] blocks for the nibble-parse chains
    (mirror of Lean li_blt_nt/li_bge_nt/li_bge_t/li_blt_t).  Operands are
    bytes (< 256 < 2^63) so signed/unsigned compare agree ([sltb_small]). *)

(* [li t3,K; blt t2,t3] with c >= K: blt NOT taken, 2 steps to off+8. *)
Lemma li_blt_nt s off K c imm :
  CodeLoaded s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> rget s 7 = c ->
  decode (wordAt off) = Iaddi 28 0 K -> decode (wordAt (off + 4)) = Iblt 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 -> K <= c ->
  runUntil 0 2 s = setPc (rset s 28 K) (coreAddr + (off + 8)).
Proof.
  intros hc ho hb hpc h7 hli hblt hK hcc hge. rewrite coreBytes_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length coreBytes)) by (rewrite coreBytes_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero, (wadd_id 0 K ltac:(lia)),
      Z.add_0_l, hpc, (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1) by
    (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by
    (unfold s1; rewrite (li_block_frame s K (coreAddr + (off + 4)) 7 ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by
    (unfold s1; rewrite setPc_rget, (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (hslt : sltb (rget s1 7) (rget s1 28) = false).
  { rewrite h7s1, h28s1, (sltb_small c K ltac:(lia) ltac:(lia)).
    destruct (c <? K) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]. }
  assert (hu2 : step s1 = setPc s1 (coreAddr + (off + 8))).
  { rewrite (step_blt s1 (off + 4) 7 28 imm hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1 hblt),
      hslt. cbn match. rewrite hpc1, (wadd_id (coreAddr + (off + 4)) 4 ltac:(unfold coreAddr; lia)).
    f_equal. lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2. unfold s1. reflexivity.
Qed.

(* [li t3,K; bge t2,t3] with c < K: bge NOT taken, 2 steps to off+8. *)
Lemma li_bge_nt s off K c imm :
  CodeLoaded s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> rget s 7 = c ->
  decode (wordAt off) = Iaddi 28 0 K -> decode (wordAt (off + 4)) = Ibge 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 -> c < K ->
  runUntil 0 2 s = setPc (rset s 28 K) (coreAddr + (off + 8)).
Proof.
  intros hc ho hb hpc h7 hli hbge hK hcc hlt. rewrite coreBytes_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length coreBytes)) by (rewrite coreBytes_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero, (wadd_id 0 K ltac:(lia)),
      Z.add_0_l, hpc, (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1) by
    (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by
    (unfold s1; rewrite (li_block_frame s K (coreAddr + (off + 4)) 7 ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by
    (unfold s1; rewrite setPc_rget, (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (hslt : sltb (rget s1 7) (rget s1 28) = true).
  { rewrite h7s1, h28s1, (sltb_small c K ltac:(lia) ltac:(lia)). apply Z.ltb_lt. lia. }
  assert (hu2 : step s1 = setPc s1 (coreAddr + (off + 8))).
  { rewrite (step_bge s1 (off + 4) 7 28 imm hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1 hbge),
      hslt. cbn match. rewrite hpc1, (wadd_id (coreAddr + (off + 4)) 4 ltac:(unfold coreAddr; lia)).
    f_equal. lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2. unfold s1. reflexivity.
Qed.

(* [li t3,K; bge t2,t3] with c >= K: bge IS taken to [target]. *)
Lemma li_bge_t s off K c imm target :
  CodeLoaded s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> rget s 7 = c ->
  decode (wordAt off) = Iaddi 28 0 K -> decode (wordAt (off + 4)) = Ibge 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 -> K <= c ->
  wadd (coreAddr + (off + 4)) imm = target ->
  runUntil 0 2 s = setPc (rset s 28 K) target.
Proof.
  intros hc ho hb hpc h7 hli hbge hK hcc hge htgt. rewrite coreBytes_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length coreBytes)) by (rewrite coreBytes_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero, (wadd_id 0 K ltac:(lia)),
      Z.add_0_l, hpc, (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1) by
    (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by
    (unfold s1; rewrite (li_block_frame s K (coreAddr + (off + 4)) 7 ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by
    (unfold s1; rewrite setPc_rget, (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (hslt : sltb (rget s1 7) (rget s1 28) = false).
  { rewrite h7s1, h28s1, (sltb_small c K ltac:(lia) ltac:(lia)).
    destruct (c <? K) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]. }
  assert (hu2 : step s1 = setPc s1 target).
  { rewrite (step_bge s1 (off + 4) 7 28 imm hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1 hbge),
      hslt. cbn match. rewrite hpc1, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2. unfold s1. reflexivity.
Qed.

(* [li t3,K; blt t2,t3] with c < K: blt IS taken to [target]. *)
Lemma li_blt_t s off K c imm target :
  CodeLoaded s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> rget s 7 = c ->
  decode (wordAt off) = Iaddi 28 0 K -> decode (wordAt (off + 4)) = Iblt 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 -> c < K ->
  wadd (coreAddr + (off + 4)) imm = target ->
  runUntil 0 2 s = setPc (rset s 28 K) target.
Proof.
  intros hc ho hb hpc h7 hli hblt hK hcc hlt htgt. rewrite coreBytes_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length coreBytes)) by (rewrite coreBytes_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero, (wadd_id 0 K ltac:(lia)),
      Z.add_0_l, hpc, (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1) by
    (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by
    (unfold s1; rewrite (li_block_frame s K (coreAddr + (off + 4)) 7 ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by
    (unfold s1; rewrite setPc_rget, (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (hslt : sltb (rget s1 7) (rget s1 28) = true).
  { rewrite h7s1, h28s1, (sltb_small c K ltac:(lia) ltac:(lia)). apply Z.ltb_lt. lia. }
  assert (hu2 : step s1 = setPc s1 target).
  { rewrite (step_blt s1 (off + 4) 7 28 imm hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1 hblt),
      hslt. cbn match. rewrite hpc1, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2. unfold s1. reflexivity.
Qed.

(** ** The high/low beq fall-through chains (mirror of high_beq_ft/low_beq_ft).
    All five [li K; beq] blocks fall through (c is none of the stop chars). *)

(* High beq-chain (offsets 24..60): c not a space/comment char -> reach 64. *)
Lemma high_beq_ft s c :
  CodeLoaded s -> s.(pc) = coreAddr + 24 -> rget s 7 = c -> 0 <= c < 256 ->
  c <> 35 -> c <> 59 -> c <> 10 -> c <> 32 -> c <> 95 ->
  (runUntil 0 10 s).(pc) = coreAddr + 64 /\ (runUntil 0 10 s).(mem) = s.(mem) /\
  (forall i, i <> 28 -> rget (runUntil 0 10 s) i = rget s i).
Proof.
  intros hcode hpc h7 hc h35 h59 h10 h32 h95.
  pose proof (li_beq_ne s 24 35 c 208 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h35) as b1.
  set (sb := setPc (rset s 28 35) (coreAddr + (24 + 8))) in *.
  assert (hcb : CodeLoaded sb) by
    (apply (CodeLoaded_eqmem s); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcb : sb.(pc) = coreAddr + 32) by (unfold sb; reflexivity).
  assert (h7b : rget sb 7 = c) by
    (unfold sb; rewrite (li_block_frame s 35 (coreAddr + (24 + 8)) 7 ltac:(lia)); exact h7).
  pose proof (li_beq_ne sb 32 59 c 200 hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb h7b
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h59) as b2.
  set (sc := setPc (rset sb 28 59) (coreAddr + (32 + 8))) in *.
  assert (hcc : CodeLoaded sc) by
    (apply (CodeLoaded_eqmem s); [unfold sc; rewrite setPc_mem, rset_mem; unfold sb;
       rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcc : sc.(pc) = coreAddr + 40) by (unfold sc; reflexivity).
  assert (h7c : rget sc 7 = c) by
    (unfold sc; rewrite (li_block_frame sb 59 (coreAddr + (32 + 8)) 7 ltac:(lia)); exact h7b).
  pose proof (li_beq_ne sc 40 10 c (-36) hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcc h7c
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h10) as b3.
  set (sd := setPc (rset sc 28 10) (coreAddr + (40 + 8))) in *.
  assert (hcd : CodeLoaded sd) by
    (apply (CodeLoaded_eqmem s); [unfold sd; rewrite setPc_mem, rset_mem; unfold sc;
       rewrite setPc_mem, rset_mem; unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcd : sd.(pc) = coreAddr + 48) by (unfold sd; reflexivity).
  assert (h7d : rget sd 7 = c) by
    (unfold sd; rewrite (li_block_frame sc 10 (coreAddr + (40 + 8)) 7 ltac:(lia)); exact h7c).
  pose proof (li_beq_ne sd 48 32 c (-44) hcd ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcd h7d
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h32) as b4.
  set (se := setPc (rset sd 28 32) (coreAddr + (48 + 8))) in *.
  assert (hce : CodeLoaded se) by
    (apply (CodeLoaded_eqmem s); [unfold se; rewrite setPc_mem, rset_mem; unfold sd;
       rewrite setPc_mem, rset_mem; unfold sc; rewrite setPc_mem, rset_mem; unfold sb;
       rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpce : se.(pc) = coreAddr + 56) by (unfold se; reflexivity).
  assert (h7e : rget se 7 = c) by
    (unfold se; rewrite (li_block_frame sd 32 (coreAddr + (48 + 8)) 7 ltac:(lia)); exact h7d).
  pose proof (li_beq_ne se 56 95 c (-52) hce ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpce h7e
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h95) as b5.
  assert (hfin : runUntil 0 10 s = setPc (rset se 28 95) (coreAddr + (56 + 8)))
    by (rewrite (runUntil_add 2 8), b1, (runUntil_add 2 6), b2, (runUntil_add 2 4), b3,
        (runUntil_add 2 2), b4, b5; reflexivity).
  rewrite hfin. repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_mem, rset_mem. unfold se. rewrite setPc_mem, rset_mem. unfold sd.
    rewrite setPc_mem, rset_mem. unfold sc. rewrite setPc_mem, rset_mem. unfold sb.
    rewrite setPc_mem, rset_mem. reflexivity.
  - intros i hi. rewrite (li_block_frame se 95 (coreAddr + (56 + 8)) i hi).
    unfold se. rewrite (li_block_frame sd 32 (coreAddr + (48 + 8)) i hi).
    unfold sd. rewrite (li_block_frame sc 10 (coreAddr + (40 + 8)) i hi).
    unfold sc. rewrite (li_block_frame sb 59 (coreAddr + (32 + 8)) i hi).
    unfold sb. rewrite (li_block_frame s 35 (coreAddr + (24 + 8)) i hi). reflexivity.
Qed.

(* Low-stop beq-chain (offsets 124..160): l not a stop char -> reach 164. *)
Lemma low_beq_ft s c :
  CodeLoaded s -> s.(pc) = coreAddr + 124 -> rget s 7 = c -> 0 <= c < 256 ->
  c <> 35 -> c <> 59 -> c <> 10 -> c <> 32 -> c <> 95 ->
  (runUntil 0 10 s).(pc) = coreAddr + 164 /\ (runUntil 0 10 s).(mem) = s.(mem) /\
  (forall i, i <> 28 -> rget (runUntil 0 10 s) i = rget s i).
Proof.
  intros hcode hpc h7 hc h35 h59 h10 h32 h95.
  pose proof (li_beq_ne s 124 10 c 160 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h10) as b1.
  set (sb := setPc (rset s 28 10) (coreAddr + (124 + 8))) in *.
  assert (hcb : CodeLoaded sb) by
    (apply (CodeLoaded_eqmem s); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcb : sb.(pc) = coreAddr + 132) by (unfold sb; reflexivity).
  assert (h7b : rget sb 7 = c) by
    (unfold sb; rewrite (li_block_frame s 10 (coreAddr + (124 + 8)) 7 ltac:(lia)); exact h7).
  pose proof (li_beq_ne sb 132 32 c 152 hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb h7b
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h32) as b2.
  set (sc := setPc (rset sb 28 32) (coreAddr + (132 + 8))) in *.
  assert (hcc : CodeLoaded sc) by
    (apply (CodeLoaded_eqmem s); [unfold sc; rewrite setPc_mem, rset_mem; unfold sb;
       rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcc : sc.(pc) = coreAddr + 140) by (unfold sc; reflexivity).
  assert (h7c : rget sc 7 = c) by
    (unfold sc; rewrite (li_block_frame sb 32 (coreAddr + (132 + 8)) 7 ltac:(lia)); exact h7b).
  pose proof (li_beq_ne sc 140 95 c 144 hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcc h7c
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h95) as b3.
  set (sd := setPc (rset sc 28 95) (coreAddr + (140 + 8))) in *.
  assert (hcd : CodeLoaded sd) by
    (apply (CodeLoaded_eqmem s); [unfold sd; rewrite setPc_mem, rset_mem; unfold sc;
       rewrite setPc_mem, rset_mem; unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcd : sd.(pc) = coreAddr + 148) by (unfold sd; reflexivity).
  assert (h7d : rget sd 7 = c) by
    (unfold sd; rewrite (li_block_frame sc 95 (coreAddr + (140 + 8)) 7 ltac:(lia)); exact h7c).
  pose proof (li_beq_ne sd 148 35 c 136 hcd ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcd h7d
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h35) as b4.
  set (se := setPc (rset sd 28 35) (coreAddr + (148 + 8))) in *.
  assert (hce : CodeLoaded se) by
    (apply (CodeLoaded_eqmem s); [unfold se; rewrite setPc_mem, rset_mem; unfold sd;
       rewrite setPc_mem, rset_mem; unfold sc; rewrite setPc_mem, rset_mem; unfold sb;
       rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpce : se.(pc) = coreAddr + 156) by (unfold se; reflexivity).
  assert (h7e : rget se 7 = c) by
    (unfold se; rewrite (li_block_frame sd 35 (coreAddr + (148 + 8)) 7 ltac:(lia)); exact h7d).
  pose proof (li_beq_ne se 156 59 c 128 hce ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpce h7e
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h59) as b5.
  assert (hfin : runUntil 0 10 s = setPc (rset se 28 59) (coreAddr + (156 + 8)))
    by (rewrite (runUntil_add 2 8), b1, (runUntil_add 2 6), b2, (runUntil_add 2 4), b3,
        (runUntil_add 2 2), b4, b5; reflexivity).
  rewrite hfin. repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_mem, rset_mem. unfold se. rewrite setPc_mem, rset_mem. unfold sd.
    rewrite setPc_mem, rset_mem. unfold sc. rewrite setPc_mem, rset_mem. unfold sb.
    rewrite setPc_mem, rset_mem. reflexivity.
  - intros i hi. rewrite (li_block_frame se 59 (coreAddr + (156 + 8)) i hi).
    unfold se. rewrite (li_block_frame sd 35 (coreAddr + (148 + 8)) i hi).
    unfold sd. rewrite (li_block_frame sc 95 (coreAddr + (140 + 8)) i hi).
    unfold sc. rewrite (li_block_frame sb 32 (coreAddr + (132 + 8)) i hi).
    unfold sb. rewrite (li_block_frame s 10 (coreAddr + (124 + 8)) i hi). reflexivity.
Qed.

(** ** Nibble helpers + the high/low nibble-parse chains. *)

(* nibble (as Z byte): digit '0'..'9' -> c-48, letter 'A'..'F' -> c-55. *)
Lemma nibble_cases c hi : 0 <= c -> nibble (Z.to_nat c) = Some hi ->
  (48 <= c <= 57 /\ c - 48 = Z.of_nat hi) \/ (65 <= c <= 70 /\ c - 55 = Z.of_nat hi).
Proof.
  intros h0 hn.
  assert (Hc : c = Z.of_nat (Z.to_nat c)) by (rewrite Z2Nat.id; [reflexivity| exact h0]).
  unfold nibble in hn. set (n := Z.to_nat c) in *.
  destruct ((48 <=? n) && (n <=? 57))%nat eqn:Ed.
  - apply andb_true_iff in Ed. destruct Ed as [E1 E2].
    apply Nat.leb_le in E1. apply Nat.leb_le in E2. cbv iota in hn. injection hn as hn.
    left. split; [rewrite Hc; lia|]. rewrite Hc, <- hn, Nat2Z.inj_sub by lia. reflexivity.
  - destruct ((65 <=? n) && (n <=? 70))%nat eqn:El.
    + apply andb_true_iff in El. destruct El as [E1 E2].
      apply Nat.leb_le in E1. apply Nat.leb_le in E2. cbv iota in hn. injection hn as hn.
      right. split; [rewrite Hc; lia|]. rewrite Hc, <- hn, Nat2Z.inj_sub by lia. reflexivity.
    + cbv iota in hn. discriminate hn.
Qed.

Lemma nibble_lt c hi : nibble c = Some hi -> (hi < 16)%nat.
Proof.
  unfold nibble. destruct ((48 <=? c) && (c <=? 57))%nat eqn:Ed.
  - apply andb_true_iff in Ed. destruct Ed as [E1 E2].
    apply Nat.leb_le in E1. apply Nat.leb_le in E2. intros H; injection H as H; lia.
  - destruct ((65 <=? c) && (c <=? 70))%nat eqn:El.
    + apply andb_true_iff in El. destruct El as [E1 E2].
      apply Nat.leb_le in E1. apply Nat.leb_le in E2. intros H; injection H as H; lia.
    + discriminate.
Qed.

(* High-nibble parse (offsets 64..104): nibble c = Some hi -> reach have_high
   (108) with t4 (x29) = hi.  Mirror of Lean [high_parse]. *)
Lemma high_parse s c hi :
  CodeLoaded s -> s.(pc) = coreAddr + 64 -> rget s 7 = c -> 0 <= c < 256 ->
  nibble (Z.to_nat c) = Some hi ->
  exists k, (runUntil 0 k s).(pc) = coreAddr + 108 /\ (runUntil 0 k s).(mem) = s.(mem) /\
    rget (runUntil 0 k s) 29 = Z.of_nat hi /\
    (forall i, i <> 28 -> i <> 29 -> rget (runUntil 0 k s) i = rget s i).
Proof.
  intros hcode hpc h7 hc hn.
  destruct (nibble_cases c hi ltac:(lia) hn) as [[Hr Hv]|[Hr Hv]].
  - (* digit *)
    pose proof (li_blt_nt s 64 48 c 244 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bA.
    set (s_a := setPc (rset s 28 48) (coreAddr + (64 + 8))) in *.
    assert (hca : CodeLoaded s_a) by
      (apply (CodeLoaded_eqmem s); [unfold s_a; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : s_a.(pc) = coreAddr + 72) by (unfold s_a; reflexivity).
    assert (h7a : rget s_a 7 = c) by
      (unfold s_a; rewrite (li_block_frame s 48 (coreAddr + (64 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_bge_nt s_a 72 58 c 12 hca ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpca h7a
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bB.
    set (s_b := setPc (rset s_a 28 58) (coreAddr + (72 + 8))) in *.
    assert (hcb : CodeLoaded s_b) by
      (apply (CodeLoaded_eqmem s_a); [unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : s_b.(pc) = coreAddr + 80) by (unfold s_b; reflexivity).
    assert (h7b : rget s_b 7 = c) by
      (unfold s_b; rewrite (li_block_frame s_a 58 (coreAddr + (72 + 8)) 7 ltac:(lia)); exact h7a).
    assert (haddi : step s_b = setPc (rset s_b 29 (c + -48)) (coreAddr + 84)).
    { rewrite (step_addi s_b 80 29 7 (-48) hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb
        ltac:(vm_compute; reflexivity)), h7b, (wadd_id c (-48) ltac:(lia)), hpcb,
        (wadd_id (coreAddr + 80) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
    set (s_c := setPc (rset s_b 29 (c + -48)) (coreAddr + 84)) in *.
    assert (hcc : CodeLoaded s_c) by
      (apply (CodeLoaded_eqmem s_b); [unfold s_c; rewrite setPc_mem, rset_mem; reflexivity| exact hcb]).
    assert (hpcc : s_c.(pc) = coreAddr + 84) by (unfold s_c; reflexivity).
    assert (hjal : step s_c = setPc s_c (coreAddr + 108)).
    { rewrite (step_jal s_c 84 0 24 hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcc
        ltac:(vm_compute; reflexivity)).
      assert (Hr0 : rset s_c 0 (wadd s_c.(pc) 4) = s_c) by (unfold rset; reflexivity).
      rewrite Hr0, hpcc, (wadd_id (coreAddr + 84) 24 ltac:(unfold coreAddr; lia)). reflexivity. }
    assert (hbc : runUntil 0 2 s_b = setPc s_c (coreAddr + 108)).
    { assert (hpb0 : s_b.(pc) <> 0) by (rewrite hpcb; apply coreAddr_pos; lia).
      assert (hpc0 : s_c.(pc) <> 0) by (rewrite hpcc; apply coreAddr_pos; lia).
      rewrite (runUntil_S 1 s_b hpb0), haddi, (runUntil_S 0 s_c hpc0), hjal. reflexivity. }
    assert (hfin : runUntil 0 (2 + (2 + 2)) s = setPc s_c (coreAddr + 108))
      by (rewrite (runUntil_add 2 (2 + 2)), bA, (runUntil_add 2 2), bB, hbc; reflexivity).
    exists (2 + (2 + 2))%nat. rewrite hfin. repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem. unfold s_c. rewrite setPc_mem, rset_mem. unfold s_b.
      rewrite setPc_mem, rset_mem. unfold s_a. rewrite setPc_mem, rset_mem. reflexivity.
    + rewrite setPc_rget. unfold s_c.
      rewrite setPc_rget, (rset_rget s_b 29 (c + -48) 29 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
    + intros i hi28 hi29. rewrite setPc_rget. unfold s_c. rewrite setPc_rget.
      destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
      apply Z.eqb_neq in E0. rewrite (rset_rget s_b 29 (c + -48) i ltac:(lia) E0).
      replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact hi29).
      unfold s_b. rewrite (li_block_frame s_a 58 (coreAddr + (72 + 8)) i hi28).
      unfold s_a. rewrite (li_block_frame s 48 (coreAddr + (64 + 8)) i hi28). reflexivity.
  - (* letter *)
    pose proof (li_blt_nt s 64 48 c 244 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bA.
    set (s_a := setPc (rset s 28 48) (coreAddr + (64 + 8))) in *.
    assert (hca : CodeLoaded s_a) by
      (apply (CodeLoaded_eqmem s); [unfold s_a; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : s_a.(pc) = coreAddr + 72) by (unfold s_a; reflexivity).
    assert (h7a : rget s_a 7 = c) by
      (unfold s_a; rewrite (li_block_frame s 48 (coreAddr + (64 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_bge_t s_a 72 58 c 12 (coreAddr + 88) hca ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpca h7a ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (72 + 4)) 12 ltac:(unfold coreAddr; lia)); lia)) as bB.
    set (s_b := setPc (rset s_a 28 58) (coreAddr + 88)) in *.
    assert (hcb : CodeLoaded s_b) by
      (apply (CodeLoaded_eqmem s_a); [unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : s_b.(pc) = coreAddr + 88) by (unfold s_b; reflexivity).
    assert (h7b : rget s_b 7 = c) by
      (unfold s_b; rewrite (li_block_frame s_a 58 (coreAddr + 88) 7 ltac:(lia)); exact h7a).
    pose proof (li_blt_nt s_b 88 65 c 220 hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb h7b
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bC.
    set (s_c := setPc (rset s_b 28 65) (coreAddr + (88 + 8))) in *.
    assert (hcc : CodeLoaded s_c) by
      (apply (CodeLoaded_eqmem s_b); [unfold s_c; rewrite setPc_mem, rset_mem; reflexivity| exact hcb]).
    assert (hpcc : s_c.(pc) = coreAddr + 96) by (unfold s_c; reflexivity).
    assert (h7c : rget s_c 7 = c) by
      (unfold s_c; rewrite (li_block_frame s_b 65 (coreAddr + (88 + 8)) 7 ltac:(lia)); exact h7b).
    pose proof (li_bge_nt s_c 96 71 c 212 hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcc h7c
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bD.
    set (s_d := setPc (rset s_c 28 71) (coreAddr + (96 + 8))) in *.
    assert (hcd : CodeLoaded s_d) by
      (apply (CodeLoaded_eqmem s_c); [unfold s_d; rewrite setPc_mem, rset_mem; reflexivity| exact hcc]).
    assert (hpcd : s_d.(pc) = coreAddr + 104) by (unfold s_d; reflexivity).
    assert (h7d : rget s_d 7 = c) by
      (unfold s_d; rewrite (li_block_frame s_c 71 (coreAddr + (96 + 8)) 7 ltac:(lia)); exact h7c).
    assert (haddi : step s_d = setPc (rset s_d 29 (c + -55)) (coreAddr + 108)).
    { rewrite (step_addi s_d 104 29 7 (-55) hcd ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcd
        ltac:(vm_compute; reflexivity)), h7d, (wadd_id c (-55) ltac:(lia)), hpcd,
        (wadd_id (coreAddr + 104) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
    assert (hpd0 : s_d.(pc) <> 0) by (rewrite hpcd; apply coreAddr_pos; lia).
    assert (hfin : runUntil 0 (2 + (2 + (2 + (2 + 1)))) s = setPc (rset s_d 29 (c + -55)) (coreAddr + 108))
      by (rewrite (runUntil_add 2 (2 + (2 + (2 + 1)))), bA, (runUntil_add 2 (2 + (2 + 1))), bB,
          (runUntil_add 2 (2 + 1)), bC, (runUntil_add 2 1), bD, (runUntil_one s_d hpd0), haddi;
          reflexivity).
    exists (2 + (2 + (2 + (2 + 1))))%nat. rewrite hfin. repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_d. rewrite setPc_mem, rset_mem. unfold s_c.
      rewrite setPc_mem, rset_mem. unfold s_b. rewrite setPc_mem, rset_mem. unfold s_a.
      rewrite setPc_mem, rset_mem. reflexivity.
    + rewrite setPc_rget, (rset_rget s_d 29 (c + -55) 29 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
    + intros i hi28 hi29. rewrite setPc_rget.
      destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
      apply Z.eqb_neq in E0. rewrite (rset_rget s_d 29 (c + -55) i ltac:(lia) E0).
      replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact hi29).
      unfold s_d. rewrite (li_block_frame s_c 71 (coreAddr + (96 + 8)) i hi28).
      unfold s_c. rewrite (li_block_frame s_b 65 (coreAddr + (88 + 8)) i hi28).
      unfold s_b. rewrite (li_block_frame s_a 58 (coreAddr + 88) i hi28).
      unfold s_a. rewrite (li_block_frame s 48 (coreAddr + (64 + 8)) i hi28). reflexivity.
Qed.

(* Low-nibble parse (offsets 164..204): nibble c = Some lo -> reach have_low
   (208) with t5 (x30) = lo.  Mirror of [high_parse] (reg 30, offsets +100). *)
Lemma low_parse s c lo :
  CodeLoaded s -> s.(pc) = coreAddr + 164 -> rget s 7 = c -> 0 <= c < 256 ->
  nibble (Z.to_nat c) = Some lo ->
  exists k, (runUntil 0 k s).(pc) = coreAddr + 208 /\ (runUntil 0 k s).(mem) = s.(mem) /\
    rget (runUntil 0 k s) 30 = Z.of_nat lo /\
    (forall i, i <> 28 -> i <> 30 -> rget (runUntil 0 k s) i = rget s i).
Proof.
  intros hcode hpc h7 hc hn.
  destruct (nibble_cases c lo ltac:(lia) hn) as [[Hr Hv]|[Hr Hv]].
  - (* digit *)
    pose proof (li_blt_nt s 164 48 c 144 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bA.
    set (s_a := setPc (rset s 28 48) (coreAddr + (164 + 8))) in *.
    assert (hca : CodeLoaded s_a) by
      (apply (CodeLoaded_eqmem s); [unfold s_a; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : s_a.(pc) = coreAddr + 172) by (unfold s_a; reflexivity).
    assert (h7a : rget s_a 7 = c) by
      (unfold s_a; rewrite (li_block_frame s 48 (coreAddr + (164 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_bge_nt s_a 172 58 c 12 hca ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpca h7a
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bB.
    set (s_b := setPc (rset s_a 28 58) (coreAddr + (172 + 8))) in *.
    assert (hcb : CodeLoaded s_b) by
      (apply (CodeLoaded_eqmem s_a); [unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : s_b.(pc) = coreAddr + 180) by (unfold s_b; reflexivity).
    assert (h7b : rget s_b 7 = c) by
      (unfold s_b; rewrite (li_block_frame s_a 58 (coreAddr + (172 + 8)) 7 ltac:(lia)); exact h7a).
    assert (haddi : step s_b = setPc (rset s_b 30 (c + -48)) (coreAddr + 184)).
    { rewrite (step_addi s_b 180 30 7 (-48) hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb
        ltac:(vm_compute; reflexivity)), h7b, (wadd_id c (-48) ltac:(lia)), hpcb,
        (wadd_id (coreAddr + 180) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
    set (s_c := setPc (rset s_b 30 (c + -48)) (coreAddr + 184)) in *.
    assert (hcc : CodeLoaded s_c) by
      (apply (CodeLoaded_eqmem s_b); [unfold s_c; rewrite setPc_mem, rset_mem; reflexivity| exact hcb]).
    assert (hpcc : s_c.(pc) = coreAddr + 184) by (unfold s_c; reflexivity).
    assert (hjal : step s_c = setPc s_c (coreAddr + 208)).
    { rewrite (step_jal s_c 184 0 24 hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcc
        ltac:(vm_compute; reflexivity)).
      assert (Hr0 : rset s_c 0 (wadd s_c.(pc) 4) = s_c) by (unfold rset; reflexivity).
      rewrite Hr0, hpcc, (wadd_id (coreAddr + 184) 24 ltac:(unfold coreAddr; lia)). reflexivity. }
    assert (hbc : runUntil 0 2 s_b = setPc s_c (coreAddr + 208)).
    { assert (hpb0 : s_b.(pc) <> 0) by (rewrite hpcb; apply coreAddr_pos; lia).
      assert (hpc0 : s_c.(pc) <> 0) by (rewrite hpcc; apply coreAddr_pos; lia).
      rewrite (runUntil_S 1 s_b hpb0), haddi, (runUntil_S 0 s_c hpc0), hjal. reflexivity. }
    assert (hfin : runUntil 0 (2 + (2 + 2)) s = setPc s_c (coreAddr + 208))
      by (rewrite (runUntil_add 2 (2 + 2)), bA, (runUntil_add 2 2), bB, hbc; reflexivity).
    exists (2 + (2 + 2))%nat. rewrite hfin. repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem. unfold s_c. rewrite setPc_mem, rset_mem. unfold s_b.
      rewrite setPc_mem, rset_mem. unfold s_a. rewrite setPc_mem, rset_mem. reflexivity.
    + rewrite setPc_rget. unfold s_c.
      rewrite setPc_rget, (rset_rget s_b 30 (c + -48) 30 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
    + intros i hi28 hi30. rewrite setPc_rget. unfold s_c. rewrite setPc_rget.
      destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
      apply Z.eqb_neq in E0. rewrite (rset_rget s_b 30 (c + -48) i ltac:(lia) E0).
      replace (i =? 30) with false by (symmetry; apply Z.eqb_neq; exact hi30).
      unfold s_b. rewrite (li_block_frame s_a 58 (coreAddr + (172 + 8)) i hi28).
      unfold s_a. rewrite (li_block_frame s 48 (coreAddr + (164 + 8)) i hi28). reflexivity.
  - (* letter *)
    pose proof (li_blt_nt s 164 48 c 144 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bA.
    set (s_a := setPc (rset s 28 48) (coreAddr + (164 + 8))) in *.
    assert (hca : CodeLoaded s_a) by
      (apply (CodeLoaded_eqmem s); [unfold s_a; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : s_a.(pc) = coreAddr + 172) by (unfold s_a; reflexivity).
    assert (h7a : rget s_a 7 = c) by
      (unfold s_a; rewrite (li_block_frame s 48 (coreAddr + (164 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_bge_t s_a 172 58 c 12 (coreAddr + 188) hca ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpca h7a ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (172 + 4)) 12 ltac:(unfold coreAddr; lia)); lia)) as bB.
    set (s_b := setPc (rset s_a 28 58) (coreAddr + 188)) in *.
    assert (hcb : CodeLoaded s_b) by
      (apply (CodeLoaded_eqmem s_a); [unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : s_b.(pc) = coreAddr + 188) by (unfold s_b; reflexivity).
    assert (h7b : rget s_b 7 = c) by
      (unfold s_b; rewrite (li_block_frame s_a 58 (coreAddr + 188) 7 ltac:(lia)); exact h7a).
    pose proof (li_blt_nt s_b 188 65 c 120 hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb h7b
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bC.
    set (s_c := setPc (rset s_b 28 65) (coreAddr + (188 + 8))) in *.
    assert (hcc : CodeLoaded s_c) by
      (apply (CodeLoaded_eqmem s_b); [unfold s_c; rewrite setPc_mem, rset_mem; reflexivity| exact hcb]).
    assert (hpcc : s_c.(pc) = coreAddr + 196) by (unfold s_c; reflexivity).
    assert (h7c : rget s_c 7 = c) by
      (unfold s_c; rewrite (li_block_frame s_b 65 (coreAddr + (188 + 8)) 7 ltac:(lia)); exact h7b).
    pose proof (li_bge_nt s_c 196 71 c 112 hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcc h7c
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bD.
    set (s_d := setPc (rset s_c 28 71) (coreAddr + (196 + 8))) in *.
    assert (hcd : CodeLoaded s_d) by
      (apply (CodeLoaded_eqmem s_c); [unfold s_d; rewrite setPc_mem, rset_mem; reflexivity| exact hcc]).
    assert (hpcd : s_d.(pc) = coreAddr + 204) by (unfold s_d; reflexivity).
    assert (h7d : rget s_d 7 = c) by
      (unfold s_d; rewrite (li_block_frame s_c 71 (coreAddr + (196 + 8)) 7 ltac:(lia)); exact h7c).
    assert (haddi : step s_d = setPc (rset s_d 30 (c + -55)) (coreAddr + 208)).
    { rewrite (step_addi s_d 204 30 7 (-55) hcd ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcd
        ltac:(vm_compute; reflexivity)), h7d, (wadd_id c (-55) ltac:(lia)), hpcd,
        (wadd_id (coreAddr + 204) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
    assert (hpd0 : s_d.(pc) <> 0) by (rewrite hpcd; apply coreAddr_pos; lia).
    assert (hfin : runUntil 0 (2 + (2 + (2 + (2 + 1)))) s = setPc (rset s_d 30 (c + -55)) (coreAddr + 208))
      by (rewrite (runUntil_add 2 (2 + (2 + (2 + 1)))), bA, (runUntil_add 2 (2 + (2 + 1))), bB,
          (runUntil_add 2 (2 + 1)), bC, (runUntil_add 2 1), bD, (runUntil_one s_d hpd0), haddi;
          reflexivity).
    exists (2 + (2 + (2 + (2 + 1))))%nat. rewrite hfin. repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_d. rewrite setPc_mem, rset_mem. unfold s_c.
      rewrite setPc_mem, rset_mem. unfold s_b. rewrite setPc_mem, rset_mem. unfold s_a.
      rewrite setPc_mem, rset_mem. reflexivity.
    + rewrite setPc_rget, (rset_rget s_d 30 (c + -55) 30 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
    + intros i hi28 hi30. rewrite setPc_rget.
      destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
      apply Z.eqb_neq in E0. rewrite (rset_rget s_d 30 (c + -55) i ltac:(lia) E0).
      replace (i =? 30) with false by (symmetry; apply Z.eqb_neq; exact hi30).
      unfold s_d. rewrite (li_block_frame s_c 71 (coreAddr + (196 + 8)) i hi28).
      unfold s_c. rewrite (li_block_frame s_b 65 (coreAddr + (188 + 8)) i hi28).
      unfold s_b. rewrite (li_block_frame s_a 58 (coreAddr + 188) i hi28).
      unfold s_a. rewrite (li_block_frame s 48 (coreAddr + (164 + 8)) i hi28). reflexivity.
Qed.

(** ** The byte store epilogue (mirror of combine_nibbles/store_epilogue). *)

(* low nibble [lo] and high-shifted nibble [16*hi] share no bits. *)
Lemma land_hilo hi lo : 0 <= hi -> 0 <= lo < 16 -> Z.land (16 * hi) lo = 0.
Proof.
  intros Hh Hl. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec, Z.bits_0. apply andb_false_iff.
  destruct (k <? 4) eqn:Ek.
  - apply Z.ltb_lt in Ek. left.
    replace (16 * hi) with (Z.shiftl hi 4) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    rewrite Z.shiftl_spec by lia. apply Z.testbit_neg_r. lia.
  - apply Z.ltb_ge in Ek. right.
    apply Z.testbit_false. lia. rewrite Z.div_small; [reflexivity|].
    split; [lia|]. apply Z.lt_le_trans with (2 ^ 4); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* the assembled byte [(hi<<4) | lo], masked to 8 bits, is [hi*16+lo]. *)
Lemma combine_nibbles hi lo : (hi < 16)%nat -> (lo < 16)%nat ->
  (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo)) mod 256 = Z.of_nat (hi * 16 + lo).
Proof.
  intros hh hl.
  assert (Hw : wshl (Z.of_nat hi) 4 = 16 * Z.of_nat hi).
  { unfold wshl. rewrite Z.shiftl_mul_pow2 by lia. rewrite wrap_small; [lia| lia]. }
  rewrite Hw. unfold wor.
  assert (Hlor : Z.lor (16 * Z.of_nat hi) (Z.of_nat lo) = 16 * Z.of_nat hi + Z.of_nat lo).
  { pose proof (Z.add_lor_land (16 * Z.of_nat hi) (Z.of_nat lo)) as H.
    rewrite (land_hilo (Z.of_nat hi) (Z.of_nat lo) ltac:(lia) ltac:(lia)) in H. lia. }
  rewrite Hlor, Z.mod_small; [rewrite Nat2Z.inj_add, Nat2Z.inj_mul; lia | lia].
Qed.

(* Capacity-OK store epilogue (offsets 208..232): bgeu(nt); slli;or (assemble);
   add;sb (store at outAddr+n); addi t1; jal LOOP.  Mirror of [store_epilogue]. *)
Lemma store_epilogue s hi lo n cap :
  CodeLoaded s -> s.(pc) = coreAddr + 208 ->
  rget s 6 = Z.of_nat n -> rget s 13 = cap -> rget s 12 = outAddr ->
  rget s 29 = Z.of_nat hi -> rget s 30 = Z.of_nat lo ->
  (hi < 16)%nat -> (lo < 16)%nat -> Z.of_nat n < cap -> outAddr + cap < 2 ^ 64 ->
  exists k, (runUntil 0 k s).(pc) = coreAddr + 8 /\
    rget (runUntil 0 k s) 6 = Z.of_nat (n + 1) /\
    (forall i, i <> 6 -> i <> 28 -> i <> 29 -> rget (runUntil 0 k s) i = rget s i) /\
    (forall a, (runUntil 0 k s).(mem) a =
       if a =? (outAddr + Z.of_nat n) then Z.of_nat (hi * 16 + lo) else s.(mem) a).
Proof.
  intros hcode hpc h6 h13 h12 h29 h30 hhi hlo hn hout.
  (* step 1: bgeu t1,a3 NOT taken (n < cap) *)
  assert (hult : ultb (rget s 6) (rget s 13) = true)
    by (rewrite h6, h13; unfold ultb; apply Z.ltb_lt; exact hn).
  assert (hu1 : step s = setPc s (coreAddr + 212)).
  { rewrite (step_bgeu s 208 6 13 68 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc
      ltac:(vm_compute; reflexivity)), hult. cbn match.
    rewrite hpc, (wadd_id (coreAddr + 208) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (v1 := setPc s (coreAddr + 212)) in *.
  assert (hc1 : CodeLoaded v1) by
    (apply (CodeLoaded_eqmem s); [unfold v1; rewrite setPc_mem; reflexivity| exact hcode]).
  assert (hpc1 : v1.(pc) = coreAddr + 212) by reflexivity.
  (* step 2: slli t4,t4,4 *)
  assert (h29v1 : rget v1 29 = Z.of_nat hi) by (unfold v1; rewrite setPc_rget; exact h29).
  assert (hu2 : step v1 = setPc (rset v1 29 (wshl (Z.of_nat hi) 4)) (coreAddr + 216)).
  { rewrite (step_slli v1 212 29 29 4 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1
      ltac:(vm_compute; reflexivity)), h29v1, hpc1,
      (wadd_id (coreAddr + 212) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (v2 := setPc (rset v1 29 (wshl (Z.of_nat hi) 4)) (coreAddr + 216)) in *.
  assert (hc2 : CodeLoaded v2) by
    (apply (CodeLoaded_eqmem s); [unfold v2, v1; rewrite !setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpc2 : v2.(pc) = coreAddr + 216) by reflexivity.
  (* step 3: or t4,t4,t5 *)
  assert (h29v2 : rget v2 29 = wshl (Z.of_nat hi) 4) by
    (unfold v2; rewrite setPc_rget, (rset_rget v1 29 _ 29 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (h30v2 : rget v2 30 = Z.of_nat lo).
  { unfold v2. rewrite setPc_rget, (rset_rget v1 29 _ 30 ltac:(lia) ltac:(lia)).
    replace (30 =? 29) with false by reflexivity. unfold v1. rewrite setPc_rget. exact h30. }
  assert (hu3 : step v2 = setPc (rset v2 29 (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo))) (coreAddr + 220)).
  { rewrite (step_or v2 216 29 29 30 hc2 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc2
      ltac:(vm_compute; reflexivity)), h29v2, h30v2, hpc2,
      (wadd_id (coreAddr + 216) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (v3 := setPc (rset v2 29 (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo))) (coreAddr + 220)) in *.
  assert (hc3 : CodeLoaded v3) by
    (apply (CodeLoaded_eqmem s); [unfold v3, v2, v1; rewrite !setPc_mem, !rset_mem; reflexivity| exact hcode]).
  assert (hpc3 : v3.(pc) = coreAddr + 220) by reflexivity.
  (* step 4: add t3,a2,t1  (t3 := outAddr + n) *)
  assert (h12v3 : rget v3 12 = outAddr).
  { unfold v3. rewrite setPc_rget, (rset_rget v2 29 _ 12 ltac:(lia) ltac:(lia)).
    replace (12 =? 29) with false by reflexivity. unfold v2.
    rewrite setPc_rget, (rset_rget v1 29 _ 12 ltac:(lia) ltac:(lia)).
    replace (12 =? 29) with false by reflexivity. unfold v1. rewrite setPc_rget. exact h12. }
  assert (h6v3 : rget v3 6 = Z.of_nat n).
  { unfold v3. rewrite setPc_rget, (rset_rget v2 29 _ 6 ltac:(lia) ltac:(lia)).
    replace (6 =? 29) with false by reflexivity. unfold v2.
    rewrite setPc_rget, (rset_rget v1 29 _ 6 ltac:(lia) ltac:(lia)).
    replace (6 =? 29) with false by reflexivity. unfold v1. rewrite setPc_rget. exact h6. }
  assert (hu4 : step v3 = setPc (rset v3 28 (outAddr + Z.of_nat n)) (coreAddr + 224)).
  { rewrite (step_add v3 220 28 12 6 hc3 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc3
      ltac:(vm_compute; reflexivity)), h12v3, h6v3,
      (wadd_id outAddr (Z.of_nat n) ltac:(unfold outAddr in *; lia)), hpc3,
      (wadd_id (coreAddr + 220) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (v4 := setPc (rset v3 28 (outAddr + Z.of_nat n)) (coreAddr + 224)) in *.
  assert (hmemv4 : v4.(mem) = s.(mem)) by
    (unfold v4, v3, v2, v1; rewrite !setPc_mem, !rset_mem; reflexivity).
  assert (hc4 : CodeLoaded v4) by (apply (CodeLoaded_eqmem s); [exact hmemv4| exact hcode]).
  assert (hpc4 : v4.(pc) = coreAddr + 224) by reflexivity.
  (* step 5: sb t4,0(t3) *)
  assert (h28v4 : rget v4 28 = outAddr + Z.of_nat n) by
    (unfold v4; rewrite setPc_rget, (rset_rget v3 28 _ 28 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (h29v4 : rget v4 29 = wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo)).
  { unfold v4. rewrite setPc_rget, (rset_rget v3 28 _ 29 ltac:(lia) ltac:(lia)).
    replace (29 =? 28) with false by reflexivity. unfold v3.
    rewrite setPc_rget, (rset_rget v2 29 _ 29 ltac:(lia) ltac:(lia)), Z.eqb_refl. reflexivity. }
  assert (hu5 : step v4 = setPc (storeByte v4 (outAddr + Z.of_nat n)
                 (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo))) (coreAddr + 228)).
  { rewrite (step_sb v4 224 28 29 0 hc4 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc4
      ltac:(vm_compute; reflexivity)), h28v4,
      (wadd_id (outAddr + Z.of_nat n) 0 ltac:(unfold outAddr in *; lia)), Z.add_0_r, h29v4, hpc4,
      (wadd_id (coreAddr + 224) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (v5 := setPc (storeByte v4 (outAddr + Z.of_nat n)
              (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo))) (coreAddr + 228)) in *.
  assert (hc5 : CodeLoaded v5).
  { intros i Hi. assert (hile : i < 324) by (rewrite coreBytes_len in Hi; lia).
    unfold v5. rewrite setPc_mem, storeByte_mem.
    replace ((coreAddr + i) =? (outAddr + Z.of_nat n)) with false
      by (symmetry; apply Z.eqb_neq; unfold coreAddr, outAddr in *; lia).
    rewrite hmemv4. exact (hcode i Hi). }
  assert (hpc5 : v5.(pc) = coreAddr + 228) by reflexivity.
  (* step 6: addi t1,t1,1 *)
  assert (h6v5 : rget v5 6 = Z.of_nat n).
  { unfold v5. rewrite setPc_rget, storeByte_rget. unfold v4.
    rewrite setPc_rget, (rset_rget v3 28 _ 6 ltac:(lia) ltac:(lia)).
    replace (6 =? 28) with false by reflexivity. exact h6v3. }
  assert (hu6 : step v5 = setPc (rset v5 6 (Z.of_nat n + 1)) (coreAddr + 232)).
  { rewrite (step_addi v5 228 6 6 1 hc5 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc5
      ltac:(vm_compute; reflexivity)), h6v5, (wadd_id (Z.of_nat n) 1 ltac:(unfold outAddr in *; lia)), hpc5,
      (wadd_id (coreAddr + 228) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (v6 := setPc (rset v5 6 (Z.of_nat n + 1)) (coreAddr + 232)) in *.
  assert (hc6 : CodeLoaded v6) by
    (apply (CodeLoaded_eqmem v5); [unfold v6; rewrite setPc_mem, rset_mem; reflexivity| exact hc5]).
  assert (hpc6 : v6.(pc) = coreAddr + 232) by reflexivity.
  (* step 7: jal -> LOOP *)
  assert (hu7 : step v6 = setPc v6 (coreAddr + 8)).
  { rewrite (step_jal v6 232 0 (-224) hc6 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc6
      ltac:(vm_compute; reflexivity)).
    assert (Hr0 : rset v6 0 (wadd v6.(pc) 4) = v6) by (unfold rset; reflexivity).
    rewrite Hr0, hpc6, (wadd_id (coreAddr + 232) (-224) ltac:(unfold coreAddr; lia)). reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : v1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hp2 : v2.(pc) <> 0) by (rewrite hpc2; apply coreAddr_pos; lia).
  assert (hp3 : v3.(pc) <> 0) by (rewrite hpc3; apply coreAddr_pos; lia).
  assert (hp4 : v4.(pc) <> 0) by (rewrite hpc4; apply coreAddr_pos; lia).
  assert (hp5 : v5.(pc) <> 0) by (rewrite hpc5; apply coreAddr_pos; lia).
  assert (hp6 : v6.(pc) <> 0) by (rewrite hpc6; apply coreAddr_pos; lia).
  assert (hfin : runUntil 0 7 s = setPc v6 (coreAddr + 8)).
  { rewrite (runUntil_S 6 s hp0), hu1, (runUntil_S 5 v1 hp1), hu2, (runUntil_S 4 v2 hp2), hu3,
      (runUntil_S 3 v3 hp3), hu4, (runUntil_S 2 v4 hp4), hu5, (runUntil_S 1 v5 hp5), hu6,
      (runUntil_S 0 v6 hp6), hu7. reflexivity. }
  exists 7%nat. rewrite hfin. repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_rget. unfold v6.
    rewrite setPc_rget, (rset_rget v5 6 _ 6 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
  - intros i h6i h28i h29i. rewrite setPc_rget. unfold v6.
    destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
    apply Z.eqb_neq in E0. rewrite setPc_rget, (rset_rget v5 6 _ i ltac:(lia) E0).
    replace (i =? 6) with false by (symmetry; apply Z.eqb_neq; exact h6i).
    unfold v5. rewrite setPc_rget, storeByte_rget. unfold v4.
    rewrite setPc_rget, (rset_rget v3 28 _ i ltac:(lia) E0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28i).
    unfold v3. rewrite setPc_rget, (rset_rget v2 29 _ i ltac:(lia) E0).
    replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29i).
    unfold v2. rewrite setPc_rget, (rset_rget v1 29 _ i ltac:(lia) E0).
    replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29i).
    unfold v1. rewrite setPc_rget. reflexivity.
  - intros a. rewrite setPc_mem. unfold v6. rewrite setPc_mem, rset_mem. unfold v5.
    rewrite setPc_mem, storeByte_mem. destruct (a =? (outAddr + Z.of_nat n)) eqn:Ea.
    + rewrite <- (combine_nibbles hi lo hhi hlo). reflexivity.
    + rewrite hmemv4. reflexivity.
Qed.

(* Generic input-read head [bgeu(nt);add;lbu;addi] at any offset [off] of this
   shape (true at off = 8 and off = 108).  Mirror of Lean [read_prefix]. *)
Lemma read_prefix s off immB inp idx ch :
  CodeLoaded s -> s.(pc) = coreAddr + off ->
  decode (wordAt off) = Ibgeu 5 11 immB ->
  decode (wordAt (off + 4)) = Iadd 28 10 5 ->
  decode (wordAt (off + 8)) = Ilbu 7 28 0 ->
  decode (wordAt (off + 12)) = Iaddi 5 5 1 ->
  0 <= off -> off + 12 + 3 < Z.of_nat (length coreBytes) ->
  rget s 10 = inputAddr -> rget s 11 = Z.of_nat (length inp) ->
  rget s 5 = Z.of_nat idx -> (idx < length inp)%nat ->
  inputAddr + Z.of_nat (length inp) < 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat (length inp) -> s.(mem) (inputAddr + j) = nth (Z.to_nat j) inp 0) ->
  nth idx inp 0 = ch -> 0 <= ch < 256 ->
  (runUntil 0 4 s).(pc) = coreAddr + (off + 16) /\
  rget (runUntil 0 4 s) 7 = ch /\ rget (runUntil 0 4 s) 5 = rget s 5 + 1 /\
  (runUntil 0 4 s).(mem) = s.(mem) /\ CodeLoaded (runUntil 0 4 s) /\
  (forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 -> rget (runUntil 0 4 s) i = rget s i).
Proof.
  intros hcode hpc hbg hadd hlbu haddi ho hoff Ha0 Ha1 Hidx hlt hin_fit Hinmem Hch Hcr.
  rewrite coreBytes_len in hoff.
  assert (hult : ultb (rget s 5) (rget s 11) = true)
    by (rewrite Hidx, Ha1; unfold ultb; apply Z.ltb_lt; apply Nat2Z.inj_lt; exact hlt).
  assert (hs1 : step s = setPc s (coreAddr + (off + 4))).
  { rewrite (step_bgeu s off 5 11 immB hcode ho ltac:(rewrite coreBytes_len; lia) hpc hbg), hult.
    cbn match. rewrite hpc, (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s1 := setPc s (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1) by
    (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem; reflexivity| exact hcode]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (haddr : wadd (rget s1 10) (rget s1 5) = inputAddr + Z.of_nat idx).
  { unfold s1. rewrite !setPc_rget, Ha0, Hidx. apply wadd_id. unfold inputAddr in *; lia. }
  assert (hs2 : step s1 = setPc (rset s1 28 (inputAddr + Z.of_nat idx)) (coreAddr + (off + 8))).
  { rewrite (step_add s1 (off + 4) 28 10 5 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1 hadd),
      haddr, hpc1, (wadd_id (coreAddr + (off + 4)) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s2 := setPc (rset s1 28 (inputAddr + Z.of_nat idx)) (coreAddr + (off + 8))) in *.
  assert (hmem2 : s2.(mem) = s.(mem))
    by (unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem; reflexivity).
  assert (hc2 : CodeLoaded s2) by (apply (CodeLoaded_eqmem s); [exact hmem2| exact hcode]).
  assert (hpc2 : s2.(pc) = coreAddr + (off + 8)) by reflexivity.
  assert (hr28 : rget s2 28 = inputAddr + Z.of_nat idx) by
    (unfold s2; rewrite setPc_rget, (rset_rget s1 28 _ 28 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (hbyte : s2.(mem) (wadd (rget s2 28) 0) mod 256 = ch).
  { rewrite hr28, (wadd_id (inputAddr + Z.of_nat idx) 0 ltac:(unfold inputAddr in *; lia)), Z.add_0_r,
      hmem2, (Hinmem (Z.of_nat idx) ltac:(split; [lia| apply Nat2Z.inj_lt; exact hlt])), Nat2Z.id, Hch.
    apply Z.mod_small. exact Hcr. }
  assert (hs3 : step s2 = setPc (rset s2 7 ch) (coreAddr + (off + 12))).
  { rewrite (step_lbu s2 (off + 8) 7 28 0 hc2 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc2 hlbu),
      hbyte, hpc2, (wadd_id (coreAddr + (off + 8)) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s3 := setPc (rset s2 7 ch) (coreAddr + (off + 12))) in *.
  assert (hmem3 : s3.(mem) = s.(mem)) by (unfold s3; rewrite setPc_mem, rset_mem; exact hmem2).
  assert (hc3 : CodeLoaded s3) by (apply (CodeLoaded_eqmem s); [exact hmem3| exact hcode]).
  assert (hpc3 : s3.(pc) = coreAddr + (off + 12)) by reflexivity.
  assert (hr5_3 : rget s3 5 = Z.of_nat idx).
  { unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 7) with false by reflexivity.
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 28) with false by reflexivity. unfold s1. rewrite setPc_rget. exact Hidx. }
  assert (hs4 : step s3 = setPc (rset s3 5 (Z.of_nat idx + 1)) (coreAddr + (off + 16))).
  { rewrite (step_addi s3 (off + 12) 5 5 1 hc3 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc3 haddi),
      hr5_3, (wadd_id (Z.of_nat idx) 1 ltac:(unfold inputAddr in *; lia)), hpc3,
      (wadd_id (coreAddr + (off + 12)) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s4 := setPc (rset s3 5 (Z.of_nat idx + 1)) (coreAddr + (off + 16))) in *.
  assert (hmem4 : s4.(mem) = s.(mem)) by (unfold s4; rewrite setPc_mem, rset_mem; exact hmem3).
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; apply coreAddr_pos; lia).
  assert (hp3 : s3.(pc) <> 0) by (rewrite hpc3; apply coreAddr_pos; lia).
  assert (hrun : runUntil 0 4 s = s4).
  { rewrite (runUntil_S 3 s hp0), hs1, (runUntil_S 2 s1 hp1), hs2,
            (runUntil_S 1 s2 hp2), hs3, (runUntil_S 0 s3 hp3), hs4. reflexivity. }
  rewrite hrun. repeat apply conj.
  - unfold s4. apply setPc_pc.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 5 _ 7 ltac:(lia) ltac:(lia)).
    replace (7 =? 5) with false by reflexivity.
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch 7 ltac:(lia) ltac:(lia)), Z.eqb_refl. reflexivity.
  - assert (H54 : rget s4 5 = Z.of_nat idx + 1) by
      (unfold s4; rewrite setPc_rget, (rset_rget s3 5 _ 5 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
    rewrite Hidx. lia.
  - exact hmem4.
  - apply (CodeLoaded_eqmem s); [exact hmem4| exact hcode].
  - intros i h0 h5 h7 h28.
    unfold s4. rewrite setPc_rget, (rset_rget s3 5 _ i ltac:(lia) h0).
    replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch i ltac:(lia) h0).
    replace (i =? 7) with false by (symmetry; apply Z.eqb_neq; exact h7).
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ i ltac:(lia) h0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
    unfold s1. rewrite setPc_rget. reflexivity.
Qed.

(* One iteration: consume >= 1 char in <= 50 steps/char, preserving LoopInv, or
   halt correctly. The per-token dispatch (FRONTIER) -- Admitted for now. *)
Theorem loop_iteration : forall inp cap rest emitted s,
  rest <> [] -> LoopInv inp cap s rest emitted ->
  exists k,
    (exists rest' emitted', (length rest' < length rest)%nat /\
        (k <= 50 * (length rest - length rest'))%nat /\
        LoopInv inp cap (runUntil 0 k s) rest' emitted')
    \/ ((k <= 50 * length rest)%nat /\ Result (runUntil 0 k s) inp cap).
Admitted.

(* The induction (PROVED): from any LoopInv state the machine halts correctly
   within [50 * |rest| + 4] steps. The fuel-bound (point 1) made fully explicit. *)
Theorem loop_correct : forall inp cap n rest emitted s,
  (length rest <= n)%nat -> LoopInv inp cap s rest emitted ->
  Result (runUntil 0 (50 * length rest + 4) s) inp cap.
Proof.
  intros inp cap n. induction n as [|n IH]; intros rest emitted s hn hinv.
  - assert (rest = []) by (destruct rest; [reflexivity| simpl in hn; lia]).
    subst rest. exact (eof_result inp cap emitted s hinv).
  - destruct rest as [|c rest''] eqn:Er.
    + exact (eof_result inp cap emitted s hinv).
    + destruct (loop_iteration inp cap (c :: rest'') emitted s ltac:(discriminate) hinv)
        as [k [ [rest' [emitted' [Hlt [Hkb Hinv']]]] | [Hkb Hres] ]].
      * (* continue: k <= 50*(|rest|-|rest'|) chars consumed *)
        set (A := (50 * length (c :: rest'') + 4)%nat).
        assert (HkA : (k <= A)%nat) by (unfold A; lia).
        replace A with (k + (A - k))%nat by lia. rewrite runUntil_add.
        assert (HBle : (50 * length rest' + 4 <= A - k)%nat) by (unfold A; simpl length in *; lia).
        replace (A - k)%nat with ((50 * length rest' + 4) + ((A - k) - (50 * length rest' + 4)))%nat by lia.
        rewrite runUntil_add.
        assert (HIH : Result (runUntil 0 (50 * length rest' + 4) (runUntil 0 k s)) inp cap)
          by (apply (IH rest' emitted'); [simpl length in *; lia | exact Hinv']).
        rewrite (runUntil_halt _ _ (Result_pc _ _ _ HIH)). exact HIH.
      * (* halt *)
        set (A := (50 * length (c :: rest'') + 4)%nat).
        assert (HkA : (k <= A)%nat) by (unfold A; lia).
        replace A with (k + (A - k))%nat by lia. rewrite runUntil_add.
        rewrite (runUntil_halt _ _ (Result_pc _ _ _ Hres)). exact Hres.
Qed.

(** ** Well-formedness: input region fits before the output region, etc. *)
Record WellFormed (inp : list Z) (cap : Z) : Prop := {
  in_fits  : inputAddr + Z.of_nat (length inp) <= outAddr;
  out_fits : outAddr + cap < 2 ^ 64;
  bytes_ok : forall b, In b inp -> 0 <= b < 256
}.

(** ** Prologue: from the initial state, `li t0,0; li t1,0` reach the loop head
    establishing the initial invariant (full input remaining, nothing emitted). *)
Theorem init_loopinv : forall inp cap, WellFormed inp cap ->
  LoopInv inp cap (runUntil 0 2 (mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr))) inp [].
Proof.
  intros inp cap HW. destruct HW as [Hfits Hfit2 Hbytes].
  set (init := mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr)).
  assert (Hmem0 : init.(mem) = memWith inp inputAddr) by reflexivity.
  assert (Hpc0 : init.(pc) = coreAddr) by reflexivity.
  assert (Hcode0 : CodeLoaded init).
  { intros i Hi. rewrite coreBytes_len in Hi. rewrite Hmem0. unfold memWith.
    replace ((coreAddr <=? coreAddr + i) && (coreAddr + i <? coreAddr + Z.of_nat (length coreBytes)))
      with true
      by (symmetry; apply andb_true_iff; split;
          [apply Z.leb_le; lia | apply Z.ltb_lt; rewrite coreBytes_len; lia]).
    cbv iota. replace (coreAddr + i - coreAddr) with i by lia. unfold nthb. reflexivity. }
  assert (hs1 : step init = setPc (rset init 5 0) (coreAddr + 4)).
  { rewrite (step_addi init 0 5 0 0 Hcode0 ltac:(lia) ltac:(rewrite coreBytes_len; lia) Hpc0
              ltac:(vm_compute; reflexivity)).
    rewrite rget_zero, (wadd_id 0 0 ltac:(lia)), Hpc0,
            (wadd_id coreAddr 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s1 := setPc (rset init 5 0) (coreAddr + 4)) in *.
  assert (hpc1 : s1.(pc) = coreAddr + 4) by reflexivity.
  assert (hc1 : CodeLoaded s1) by (apply (CodeLoaded_eqmem init); [reflexivity| exact Hcode0]).
  assert (hs2 : step s1 = setPc (rset s1 6 0) (coreAddr + 8)).
  { rewrite (step_addi s1 4 6 0 0 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1
              ltac:(vm_compute; reflexivity)).
    rewrite rget_zero, (wadd_id 0 0 ltac:(lia)), hpc1,
            (wadd_id (coreAddr+4) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s2 := setPc (rset s1 6 0) (coreAddr + 8)) in *.
  assert (hp0 : init.(pc) <> 0) by (rewrite Hpc0; unfold coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hrun : runUntil 0 2 init = s2)
    by (rewrite (runUntil_S 1 init hp0), hs1, (runUntil_S 0 s1 hp1), hs2; reflexivity).
  rewrite hrun.
  assert (Hmem2 : s2.(mem) = memWith inp inputAddr)
    by (unfold s2, s1; rewrite !setPc_mem, !rset_mem; exact Hmem0).
  assert (R10 : rget s2 10 = inputAddr) by (unfold s2, s1, init; reflexivity).
  assert (R11 : rget s2 11 = Z.of_nat (length inp)) by (unfold s2, s1, init; reflexivity).
  assert (R12 : rget s2 12 = outAddr) by (unfold s2, s1, init; reflexivity).
  assert (R13 : rget s2 13 = cap) by (unfold s2, s1, init; reflexivity).
  assert (R1 : rget s2 1 = 0) by (unfold s2, s1, init; reflexivity).
  assert (R5 : rget s2 5 = 0) by (unfold s2, s1, init; reflexivity).
  assert (R6 : rget s2 6 = 0) by (unfold s2, s1, init; reflexivity).
  refine {| li_at_loop := _; li_code := _; li_a0 := R10; li_a1 := R11; li_a2 := R12;
            li_a3 := R13; li_ra := R1; li_in_mem := _; li_in_lt := _; li_bytes := Hbytes;
            li_in_fits := Hfits; li_out_lt := Hfit2; li_idx := _; li_suffix := _;
            li_outidx := _; li_emit_le := _; li_out_mem := _; li_spec := _ |}.
  - reflexivity.
  - apply (CodeLoaded_eqmem init); [exact Hmem2| exact Hcode0].
  - intros j Hj. rewrite Hmem2. unfold memWith.
    replace ((coreAddr <=? inputAddr + j) && (inputAddr + j <? coreAddr + Z.of_nat (length coreBytes)))
      with false
      by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge;
          rewrite coreBytes_len; unfold coreAddr, inputAddr; lia).
    cbv iota.
    replace ((inputAddr <=? inputAddr + j) && (inputAddr + j <? inputAddr + Z.of_nat (length inp)))
      with true
      by (symmetry; apply andb_true_iff; split;
          [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
    cbv iota. replace (inputAddr + j - inputAddr) with j by lia. reflexivity.
  - unfold inputAddr, outAddr in *; lia.
  - rewrite R5; lia.
  - rewrite Nat.sub_diag; reflexivity.
  - rewrite R6; reflexivity.
  - simpl; lia.
  - intros j Hj; simpl in Hj; lia.
  - rewrite app_nil_l; apply surjective_pairing.
Qed.

(** ** The general refinement theorem: PROVED modulo the per-token dispatch
    (`loop_iteration`). Mirrors the Lean assembly; the fixed 100000 fuel suffices
    because the loop halts within [2 + 50*|inp| + 4] steps and |inp| <= 484. *)
Theorem core_refines : forall (inp : list Z) (cap : Z),
  WellFormed inp cap ->
  runOn inp cap = specOn (zin inp) (Z.to_nat cap).
Proof.
  intros inp cap HW.
  assert (Hlen : (length inp <= 484)%nat)
    by (destruct HW as [Hfits _ _]; unfold inputAddr, outAddr in Hfits; lia).
  pose proof (init_loopinv inp cap HW) as HLI.
  set (init := mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr)) in *.
  pose proof (loop_correct inp cap (length inp) inp [] (runUntil 0 2 init) (le_n _) HLI) as HR.
  rewrite <- (runUntil_add 2 (50 * length inp + 4) init) in HR.
  (* The loop halts by fuel [2 + (50*|inp| + 4)] <= 100000 (since |inp| <= 484),
     so the fixed 100000-fuel run in [runOn] coincides with it. *)
  assert (HF : (2 + (50 * length inp + 4) <= 100000)%nat).
  { apply Nat2Z.inj_le.
    replace (Z.of_nat 100000) with 100000%Z by (vm_compute; reflexivity).
    lia. }
  assert (Hhalt : runUntil 0 100000 init
                  = runUntil 0 (2 + (50 * length inp + 4)) init)
    by (apply (runUntil_stab _ _ (Result_pc _ _ _ HR)); exact HF).
  unfold runOn. fold init. rewrite Hhalt.
  unfold specOn, Result in *.
  destruct (coreSpec (zin inp) (Z.to_nat cap)) as [[st bs] ln].
  destruct HR as [Hp [H10 [H11 Hmemr]]].
  rewrite H10, H11, Nat2Z.id, Hmemr. reflexivity.
Qed.
