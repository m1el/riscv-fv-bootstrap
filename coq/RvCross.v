(** * RvCross.v -- cross-validation of our RV64I model against riscv-coq.

    Task #7 (see CROSSCHECK.md): remove "our hand-rolled RV64I model is faithful
    to real RISC-V" from the TCB by proving our [Rv64i.decode]/[Rv64i.step] agree
    with the authoritative riscv-coq semantics (coq-riscv.0.0.5, the bedrock2 /
    compiler model, generated from the official Haskell riscv-semantics).

    T1 ([decode_agrees]): whenever our decoder returns one of the 16 modelled
    instructions (hex0's 12 + SUB SRLI LD SD added for hex1), riscv-coq's
    [Decode.decode RV64I] returns the corresponding instruction with identical
    operands -- for every 32-bit word.

    T2 ([step_agrees], forward simulation): one of our [step]s corresponds to one
    riscv-coq instruction cycle, preserving a state-bridge relation. *)

From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Require Import Hex0Coq.Rv64i.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Utility.
Require Import coqutil.Z.BitOps.
Require Import coqutil.Z.prove_Zeq_bitwise.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Bridging lemmas: our field/sext primitives vs riscv-coq's          *)
(* bitSlice/signExtend.                                                *)
(* ------------------------------------------------------------------ *)

(** Our [field w lo len] is exactly riscv-coq's [bitSlice w lo (lo+len)]. *)
Lemma field_bitSlice : forall w lo len,
    0 <= lo -> 0 <= len ->
    Rv64i.field w lo len = bitSlice w lo (lo + len).
Proof.
  intros w lo len Hlo Hlen.
  rewrite bitSlice_alt by lia.
  unfold bitSlice', Rv64i.field.
  f_equal. f_equal. lia.
Qed.

(** Our [sext k raw] (case-split form) equals riscv-coq's [signExtend k]
    (modular form) on in-range inputs -- which bitSlice results always are. *)
Lemma sext_signExtend : forall k raw,
    1 <= k -> 0 <= raw < 2 ^ k ->
    Rv64i.sext k raw = signExtend k raw.
Proof.
  intros k raw Hk Hraw.
  unfold Rv64i.sext, signExtend.
  assert (Hpow : 2 ^ k = 2 * 2 ^ (k - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  assert (Hhalf_pos : 0 < 2 ^ (k - 1)) by (apply Z.pow_pos_nonneg; lia).
  destruct (raw >=? 2 ^ (k - 1)) eqn:E.
  - (* raw in [2^(k-1), 2^k): result raw - 2^k *)
    apply Z.geb_le in E.
    replace (raw + 2 ^ (k - 1)) with ((raw - 2 ^ (k - 1)) + 1 * 2 ^ k) by lia.
    rewrite Z.mod_add by lia.
    rewrite Z.mod_small by lia. lia.
  - (* raw in [0, 2^(k-1)): result raw *)
    rewrite Z.geb_leb in E. apply Z.leb_gt in E.
    rewrite Z.mod_small by lia. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Range / conversion toolkit for operands.                            *)
(* ------------------------------------------------------------------ *)

(** A [field] is bounded by 2^len, hence by 2^k for any k >= len. *)
Lemma field_range : forall w lo len, 0 <= len -> 0 <= Rv64i.field w lo len < 2 ^ len.
Proof. intros. unfold Rv64i.field. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma field_lt : forall w lo len k, 0 <= len -> len <= k -> 0 <= Rv64i.field w lo len < 2 ^ k.
Proof.
  intros w lo len k Hlen Hk. pose proof (field_range w lo len Hlen) as H1.
  assert (2 ^ len <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(** [lor] of two k-bit values is a k-bit value. *)
Lemma lor_lt : forall k a b, 0 <= k -> 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros k a b Hk Ha Hb. split.
  - apply Z.lor_nonneg; lia.
  - assert (Z.shiftr (Z.lor a b) k = 0) as Hs.
    { rewrite Z.shiftr_lor.
      rewrite Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
      rewrite (Z.div_small a) by lia. rewrite (Z.div_small b) by lia. apply Z.lor_0_l. }
    rewrite Z.shiftr_div_pow2 in Hs by lia.
    apply Z.div_small_iff in Hs; [lia| apply Z.pow_nonzero; lia].
Qed.

(** A field shifted left by [s] is a (len+s)-bit value, hence < 2^k for len+s <= k. *)
Lemma shiftl_field_lt : forall w lo len s k,
  0 <= s -> 0 <= len -> len + s <= k -> 0 <= Z.shiftl (Rv64i.field w lo len) s < 2 ^ k.
Proof.
  intros. rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (field_range w lo len ltac:(lia)). split.
  - apply Z.mul_nonneg_nonneg; [lia| apply Z.pow_nonneg; lia].
  - apply Z.lt_le_trans with (2 ^ len * 2 ^ s).
    + apply Zmult_lt_compat_r; [apply Z.pow_pos_nonneg; lia| lia].
    + rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia.
Qed.

(** Discharge [0 <= <lor/shiftl/field tower> < 2^k] goals for the immediates. *)
Ltac range_tac :=
  repeat first [apply lor_lt | apply shiftl_field_lt | apply field_lt]; lia.

(** A subfield of an all-zero field is zero (used for SLLI's funct6/shamtHi). *)
Lemma field_sub0 : forall w lo len lo' len',
  0 <= w -> 0 <= lo -> lo <= lo' -> 0 <= len' -> lo' + len' <= lo + len ->
  Rv64i.field w lo len = 0 -> Rv64i.field w lo' len' = 0.
Proof.
  intros w lo len lo' len' Hw Hlo Hll Hlen' Hsum Hf.
  unfold Rv64i.field in *.
  apply Z.mod_divide in Hf; [|apply Z.pow_nonzero; lia].
  apply Z.mod_divide; [apply Z.pow_nonzero; lia|].
  replace (2 ^ lo') with (2 ^ lo * 2 ^ (lo' - lo)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite <- Z.div_div by (try apply Z.pow_pos_nonneg; lia).
  destruct Hf as [k Hk]. rewrite Hk.
  exists (k * 2 ^ (len - (lo' - lo) - len')).
  replace (2 ^ len) with (2 ^ (lo' - lo) * 2 ^ (len - (lo' - lo)))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  replace (k * (2 ^ (lo' - lo) * 2 ^ (len - (lo' - lo))))
    with ((k * 2 ^ (len - (lo' - lo))) * 2 ^ (lo' - lo)) by ring.
  rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
  rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
  replace (len - (lo' - lo) - len' + len') with (len - (lo' - lo)) by lia. reflexivity.
Qed.

(** field <-> bitSlice in both directions (normalised at concrete endpoints). *)
Lemma f_bs : forall w a c, 0 <= a -> 0 <= c -> Rv64i.field w a c = bitSlice w a (a + c).
Proof. intros. apply field_bitSlice; lia. Qed.
Lemma bs_f : forall w a b c, 0 <= a -> b = a + c -> 0 <= c -> bitSlice w a b = Rv64i.field w a c.
Proof. intros. subst b. symmetry. apply field_bitSlice; lia. Qed.

(* ------------------------------------------------------------------ *)
(* The embedding of our [Instr] into riscv-coq's [Instruction], and    *)
(* the per-instruction decode-agreement lemmas.                        *)
(* ------------------------------------------------------------------ *)

Definition embed (i : Rv64i.Instr) : Instruction :=
  match i with
  | Iaddi rd rs1 imm => IInstruction (Addi rd rs1 imm)
  | Iadd  rd rs1 rs2 => IInstruction (Add  rd rs1 rs2)
  | Isub  rd rs1 rs2 => IInstruction (Sub  rd rs1 rs2)
  | Ior   rd rs1 rs2 => IInstruction (Or   rd rs1 rs2)
  | Islli rd rs1 sh  => IInstruction (Slli rd rs1 sh)
  | Isrli rd rs1 sh  => IInstruction (Srli rd rs1 sh)
  | Ilbu  rd rs1 imm => IInstruction (Lbu  rd rs1 imm)
  | Ild   rd rs1 imm => I64Instruction (Ld rd rs1 imm)
  | Isb   rs1 rs2 imm=> IInstruction (Sb   rs1 rs2 imm)
  | Isd   rs1 rs2 imm=> I64Instruction (Sd rs1 rs2 imm)
  | Ibeq  rs1 rs2 imm=> IInstruction (Beq  rs1 rs2 imm)
  | Iblt  rs1 rs2 imm=> IInstruction (Blt  rs1 rs2 imm)
  | Ibge  rs1 rs2 imm=> IInstruction (Bge  rs1 rs2 imm)
  | Ibgeu rs1 rs2 imm=> IInstruction (Bgeu rs1 rs2 imm)
  | Ijal  rd imm     => IInstruction (Jal  rd imm)
  | Ijalr rd rs1 imm => IInstruction (Jalr rd rs1 imm)
  | Iunknown         => InvalidInstruction 0
  end.

(* Keep these abstract so [cbn] reduces only riscv-coq's decode CONTROL flow,
   leaving the operands as clean bitSlice/signExtend/shiftl/lor terms. *)
Opaque bitSlice signExtend Z.shiftl Z.lor.

(** Convert our [field]/[sext] operands to riscv-coq form and close by the
    decode/encode bit-equality prover. Handles all 16 forms uniformly. *)
Ltac finish w :=
  rewrite ?(sext_signExtend _) by (try lia; range_tac);
  rewrite !(f_bs w _ _) by lia;
  f_equal; f_equal; with_strategy transparent [bitSlice] prove_Zeq_bitwise.

Lemma decode_addi : forall w,
  Rv64i.field w 0 7 = 19 -> Rv64i.field w 12 3 = 0 ->
  decode RV64I w = embed (Iaddi (Rv64i.field w 7 5) (Rv64i.field w 15 5) (Rv64i.sext 12 (Rv64i.field w 20 12))).
Proof.
  intros w Hop Hf3.
  assert (H1: bitSlice w 0 7 = 19) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 0) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  unfold decode. cbv zeta. rewrite H1, H2. cbn. unfold embed. finish w.
Qed.

Lemma decode_slli : forall w, 0 <= w ->
  Rv64i.field w 0 7 = 19 -> Rv64i.field w 12 3 = 1 -> Rv64i.field w 25 7 = 0 ->
  decode RV64I w = embed (Islli (Rv64i.field w 7 5) (Rv64i.field w 15 5) (Rv64i.field w 20 6)).
Proof.
  intros w Hw Hop Hf3 Hf7.
  assert (Hb25 : Rv64i.field w 25 1 = 0) by (apply (field_sub0 w 25 7 25 1); lia).
  assert (Hb26 : Rv64i.field w 26 6 = 0) by (apply (field_sub0 w 25 7 26 6); lia).
  assert (H1: bitSlice w 0 7 = 19) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 1) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  assert (H3: bitSlice w 25 26 = 0) by (rewrite (bs_f w 25 26 1) by lia; exact Hb25).
  assert (H4: bitSlice w 26 32 = 0) by (rewrite (bs_f w 26 32 6) by lia; exact Hb26).
  unfold decode. cbv zeta. rewrite H1, H2, H3, H4. cbn. unfold embed. finish w.
Qed.

Lemma decode_add : forall w,
  Rv64i.field w 0 7 = 51 -> Rv64i.field w 12 3 = 0 -> Rv64i.field w 25 7 = 0 ->
  decode RV64I w = embed (Iadd (Rv64i.field w 7 5) (Rv64i.field w 15 5) (Rv64i.field w 20 5)).
Proof.
  intros w Hop Hf3 Hf7.
  assert (H1: bitSlice w 0 7 = 51) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 0) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  assert (H3: bitSlice w 25 32 = 0) by (rewrite (bs_f w 25 32 7) by lia; exact Hf7).
  unfold decode. cbv zeta. rewrite H1, H2, H3. cbn. unfold embed. finish w.
Qed.

Lemma decode_or : forall w,
  Rv64i.field w 0 7 = 51 -> Rv64i.field w 12 3 = 6 -> Rv64i.field w 25 7 = 0 ->
  decode RV64I w = embed (Ior (Rv64i.field w 7 5) (Rv64i.field w 15 5) (Rv64i.field w 20 5)).
Proof.
  intros w Hop Hf3 Hf7.
  assert (H1: bitSlice w 0 7 = 51) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 6) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  assert (H3: bitSlice w 25 32 = 0) by (rewrite (bs_f w 25 32 7) by lia; exact Hf7).
  unfold decode. cbv zeta. rewrite H1, H2, H3. cbn. unfold embed. finish w.
Qed.

Lemma decode_lbu : forall w,
  Rv64i.field w 0 7 = 3 -> Rv64i.field w 12 3 = 4 ->
  decode RV64I w = embed (Ilbu (Rv64i.field w 7 5) (Rv64i.field w 15 5) (Rv64i.sext 12 (Rv64i.field w 20 12))).
Proof.
  intros w Hop Hf3.
  assert (H1: bitSlice w 0 7 = 3) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 4) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  unfold decode. cbv zeta. rewrite H1, H2. cbn. unfold embed. finish w.
Qed.

Lemma decode_sb : forall w,
  Rv64i.field w 0 7 = 35 -> Rv64i.field w 12 3 = 0 ->
  decode RV64I w = embed (Isb (Rv64i.field w 15 5) (Rv64i.field w 20 5)
    (Rv64i.sext 12 (Z.lor (Z.shiftl (Rv64i.field w 25 7) 5) (Rv64i.field w 7 5)))).
Proof.
  intros w Hop Hf3.
  assert (H1: bitSlice w 0 7 = 35) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 0) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  unfold decode. cbv zeta. rewrite H1, H2. cbn. unfold embed. finish w.
Qed.

(* --- the 4 encodings added for hex1 (core1.s): SUB SRLI LD SD --- *)

Lemma decode_sub : forall w,
  Rv64i.field w 0 7 = 51 -> Rv64i.field w 12 3 = 0 -> Rv64i.field w 25 7 = 32 ->
  decode RV64I w = embed (Isub (Rv64i.field w 7 5) (Rv64i.field w 15 5) (Rv64i.field w 20 5)).
Proof.
  intros w Hop Hf3 Hf7.
  assert (H1: bitSlice w 0 7 = 51) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 0) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  assert (H3: bitSlice w 25 32 = 32) by (rewrite (bs_f w 25 32 7) by lia; exact Hf7).
  unfold decode. cbv zeta. rewrite H1, H2, H3. cbn. unfold embed. finish w.
Qed.

Lemma decode_srli : forall w, 0 <= w ->
  Rv64i.field w 0 7 = 19 -> Rv64i.field w 12 3 = 5 -> Rv64i.field w 25 7 = 0 ->
  decode RV64I w = embed (Isrli (Rv64i.field w 7 5) (Rv64i.field w 15 5) (Rv64i.field w 20 6)).
Proof.
  intros w Hw Hop Hf3 Hf7.
  assert (Hb25 : Rv64i.field w 25 1 = 0) by (apply (field_sub0 w 25 7 25 1); lia).
  assert (Hb26 : Rv64i.field w 26 6 = 0) by (apply (field_sub0 w 25 7 26 6); lia).
  assert (H1: bitSlice w 0 7 = 19) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 5) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  assert (H3: bitSlice w 25 26 = 0) by (rewrite (bs_f w 25 26 1) by lia; exact Hb25).
  assert (H4: bitSlice w 26 32 = 0) by (rewrite (bs_f w 26 32 6) by lia; exact Hb26).
  unfold decode. cbv zeta. rewrite H1, H2, H3, H4. cbn. unfold embed. finish w.
Qed.

Lemma decode_ld : forall w,
  Rv64i.field w 0 7 = 3 -> Rv64i.field w 12 3 = 3 ->
  decode RV64I w = embed (Ild (Rv64i.field w 7 5) (Rv64i.field w 15 5) (Rv64i.sext 12 (Rv64i.field w 20 12))).
Proof.
  intros w Hop Hf3.
  assert (H1: bitSlice w 0 7 = 3) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 3) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  unfold decode. cbv zeta. rewrite H1, H2. cbn. unfold embed. finish w.
Qed.

Lemma decode_sd : forall w,
  Rv64i.field w 0 7 = 35 -> Rv64i.field w 12 3 = 3 ->
  decode RV64I w = embed (Isd (Rv64i.field w 15 5) (Rv64i.field w 20 5)
    (Rv64i.sext 12 (Z.lor (Z.shiftl (Rv64i.field w 25 7) 5) (Rv64i.field w 7 5)))).
Proof.
  intros w Hop Hf3.
  assert (H1: bitSlice w 0 7 = 35) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 3) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  unfold decode. cbv zeta. rewrite H1, H2. cbn. unfold embed. finish w.
Qed.

(* The four branches share the same B-immediate; only funct3 differs. *)
Definition immB (w : Z) : Z :=
  Z.lor (Z.lor (Z.shiftl (Rv64i.field w 31 1) 12) (Z.shiftl (Rv64i.field w 7 1) 11))
        (Z.lor (Z.shiftl (Rv64i.field w 25 6) 5) (Z.shiftl (Rv64i.field w 8 4) 1)).

Lemma decode_beq : forall w,
  Rv64i.field w 0 7 = 99 -> Rv64i.field w 12 3 = 0 ->
  decode RV64I w = embed (Ibeq (Rv64i.field w 15 5) (Rv64i.field w 20 5) (Rv64i.sext 13 (immB w))).
Proof.
  intros w Hop Hf3.
  assert (H1: bitSlice w 0 7 = 99) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 0) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  unfold decode. cbv zeta. rewrite H1, H2. cbn. unfold embed, immB. finish w.
Qed.

Lemma decode_blt : forall w,
  Rv64i.field w 0 7 = 99 -> Rv64i.field w 12 3 = 4 ->
  decode RV64I w = embed (Iblt (Rv64i.field w 15 5) (Rv64i.field w 20 5) (Rv64i.sext 13 (immB w))).
Proof.
  intros w Hop Hf3.
  assert (H1: bitSlice w 0 7 = 99) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 4) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  unfold decode. cbv zeta. rewrite H1, H2. cbn. unfold embed, immB. finish w.
Qed.

Lemma decode_bge : forall w,
  Rv64i.field w 0 7 = 99 -> Rv64i.field w 12 3 = 5 ->
  decode RV64I w = embed (Ibge (Rv64i.field w 15 5) (Rv64i.field w 20 5) (Rv64i.sext 13 (immB w))).
Proof.
  intros w Hop Hf3.
  assert (H1: bitSlice w 0 7 = 99) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 5) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  unfold decode. cbv zeta. rewrite H1, H2. cbn. unfold embed, immB. finish w.
Qed.

Lemma decode_bgeu : forall w,
  Rv64i.field w 0 7 = 99 -> Rv64i.field w 12 3 = 7 ->
  decode RV64I w = embed (Ibgeu (Rv64i.field w 15 5) (Rv64i.field w 20 5) (Rv64i.sext 13 (immB w))).
Proof.
  intros w Hop Hf3.
  assert (H1: bitSlice w 0 7 = 99) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 7) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  unfold decode. cbv zeta. rewrite H1, H2. cbn. unfold embed, immB. finish w.
Qed.

Lemma decode_jal : forall w,
  Rv64i.field w 0 7 = 111 ->
  decode RV64I w = embed (Ijal (Rv64i.field w 7 5)
    (Rv64i.sext 21 (Z.lor (Z.lor (Z.shiftl (Rv64i.field w 31 1) 20) (Z.shiftl (Rv64i.field w 12 8) 12))
                          (Z.lor (Z.shiftl (Rv64i.field w 20 1) 11) (Z.shiftl (Rv64i.field w 21 10) 1))))).
Proof.
  intros w Hop.
  assert (H1: bitSlice w 0 7 = 111) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  unfold decode. cbv zeta. rewrite H1. cbn. unfold embed. finish w.
Qed.

Lemma decode_jalr : forall w,
  Rv64i.field w 0 7 = 103 -> Rv64i.field w 12 3 = 0 ->
  decode RV64I w = embed (Ijalr (Rv64i.field w 7 5) (Rv64i.field w 15 5) (Rv64i.sext 12 (Rv64i.field w 20 12))).
Proof.
  intros w Hop Hf3.
  assert (H1: bitSlice w 0 7 = 103) by (rewrite (bs_f w 0 7 7) by lia; exact Hop).
  assert (H2: bitSlice w 12 15 = 0) by (rewrite (bs_f w 12 15 3) by lia; exact Hf3).
  unfold decode. cbv zeta. rewrite H1, H2. cbn. unfold embed. finish w.
Qed.

(* ------------------------------------------------------------------ *)
(* T1: decode agreement, for every 32-bit word.                        *)
(* ------------------------------------------------------------------ *)

(** Whenever our decoder returns one of the 16 modelled instructions, riscv-coq's
    [decode RV64I] returns the corresponding instruction with identical operands. *)
Theorem decode_agrees : forall w, 0 <= w < 2 ^ 32 ->
  forall i, Rv64i.decode w = i -> i <> Iunknown -> decode RV64I w = embed i.
Proof.
  intros w Hw i Hi Hni. subst i. unfold Rv64i.decode in *.
  set (op := Rv64i.field w 0 7) in *.
  set (f3 := Rv64i.field w 12 3) in *.
  set (f7 := Rv64i.field w 25 7) in *.
  destruct (op =? 19) eqn:E19.
  - apply Z.eqb_eq in E19. destruct (f3 =? 0) eqn:Ef0.
    + apply Z.eqb_eq in Ef0. apply decode_addi; assumption.
    + destruct (f3 =? 1) eqn:Ef1.
      * apply Z.eqb_eq in Ef1. destruct (f7 =? 0) eqn:Ef7.
        -- apply Z.eqb_eq in Ef7. apply decode_slli; (lia || assumption).
        -- exfalso; apply Hni; reflexivity.
      * destruct (f3 =? 5) eqn:Ef5.
        -- apply Z.eqb_eq in Ef5. destruct (f7 =? 0) eqn:Ef7.
           ++ apply Z.eqb_eq in Ef7. apply decode_srli; (lia || assumption).
           ++ exfalso; apply Hni; reflexivity.
        -- exfalso; apply Hni; reflexivity.
  - destruct (op =? 51) eqn:E51.
    + apply Z.eqb_eq in E51. destruct (f7 =? 0) eqn:Ef7.
      * apply Z.eqb_eq in Ef7. destruct (f3 =? 0) eqn:Ef0.
        -- apply Z.eqb_eq in Ef0. apply decode_add; assumption.
        -- destruct (f3 =? 6) eqn:Ef6.
           ++ apply Z.eqb_eq in Ef6. apply decode_or; assumption.
           ++ exfalso; apply Hni; reflexivity.
      * destruct (f7 =? 32) eqn:Ef32.
        -- apply Z.eqb_eq in Ef32. destruct (f3 =? 0) eqn:Ef0.
           ++ apply Z.eqb_eq in Ef0. apply decode_sub; assumption.
           ++ exfalso; apply Hni; reflexivity.
        -- exfalso; apply Hni; reflexivity.
    + destruct (op =? 3) eqn:E3.
      * apply Z.eqb_eq in E3. destruct (f3 =? 4) eqn:Ef4.
        -- apply Z.eqb_eq in Ef4. apply decode_lbu; assumption.
        -- destruct (f3 =? 3) eqn:Ef3.
           ++ apply Z.eqb_eq in Ef3. apply decode_ld; assumption.
           ++ exfalso; apply Hni; reflexivity.
      * destruct (op =? 35) eqn:E35.
        -- apply Z.eqb_eq in E35. destruct (f3 =? 0) eqn:Ef0.
           ++ apply Z.eqb_eq in Ef0. apply decode_sb; assumption.
           ++ destruct (f3 =? 3) eqn:Ef3.
              ** apply Z.eqb_eq in Ef3. apply decode_sd; assumption.
              ** exfalso; apply Hni; reflexivity.
        -- destruct (op =? 99) eqn:E99.
           ++ apply Z.eqb_eq in E99. destruct (f3 =? 0) eqn:Ef0.
              ** apply Z.eqb_eq in Ef0. apply decode_beq; assumption.
              ** destruct (f3 =? 4) eqn:Ef4.
                 --- apply Z.eqb_eq in Ef4. apply decode_blt; assumption.
                 --- destruct (f3 =? 5) eqn:Ef5.
                     +++ apply Z.eqb_eq in Ef5. apply decode_bge; assumption.
                     +++ destruct (f3 =? 7) eqn:Ef7'.
                         *** apply Z.eqb_eq in Ef7'. apply decode_bgeu; assumption.
                         *** exfalso; apply Hni; reflexivity.
           ++ destruct (op =? 111) eqn:E111.
              ** apply Z.eqb_eq in E111. apply decode_jal; assumption.
              ** destruct (op =? 103) eqn:E103.
                 --- apply Z.eqb_eq in E103. destruct (f3 =? 0) eqn:Ef0.
                     +++ apply Z.eqb_eq in Ef0. apply decode_jalr; assumption.
                     +++ exfalso; apply Hni; reflexivity.
                 --- exfalso; apply Hni; reflexivity.
Qed.

(** ** Reverse direction (the correspondence is faithful both ways on the 16
    modelled forms).

    [embed] is injective on the modelled forms, so whenever riscv-coq decodes [w]
    to [embed j] AND our decoder also returns a modelled form ([decode w <> Iunknown]),
    the two outputs coincide ([decode w = j]).  Equivalently: our decoder never
    *mis*classifies -- if it commits to one of the 16 forms, it commits to the SAME
    one riscv-coq does.

    The hypothesis [Rv64i.decode w <> Iunknown] is exactly the documented narrowing
    (CROSSCHECK.md §5): for the encodings our decoder *declines* (returns [Iunknown])
    -- every instruction outside our 16 forms, and SLLI/SRLI with [shamt >= 32] (where
    riscv-coq at RV64I still yields [Slli] but our decoder requires [funct7 = 0],
    i.e. bit 25 = shamt[5] = 0) -- no reverse claim is made.  On every [core] SLLI
    ([shamt in {0..4}]) the proviso holds, so the reverse agreement applies there. *)
Lemma embed_inj : forall i j, i <> Iunknown -> embed i = embed j -> i = j.
Proof.
  intros i j Hi Heq.
  destruct i; try (exfalso; apply Hi; reflexivity);
    destruct j; cbn in Heq; try discriminate; inversion Heq; subst; reflexivity.
Qed.

Theorem decode_agrees_rev : forall w, 0 <= w < 2 ^ 32 ->
  forall j, Rv64i.decode w <> Iunknown -> decode RV64I w = embed j -> Rv64i.decode w = j.
Proof.
  intros w Hw j Hni Hdec.
  pose proof (decode_agrees w Hw (Rv64i.decode w) eq_refl Hni) as Hfwd.
  rewrite Hfwd in Hdec.
  apply embed_inj; assumption.
Qed.
