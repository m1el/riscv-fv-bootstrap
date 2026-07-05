import LowIR.ProgSim.Defs
import LowIR.ProgSim.EncodeFacts
import LowIR.ProgSim.CtrlSim

/-!
# Phase 2 (start) — the assembler layer: `Installed`'s code half from the bytes

Phase 1 (`EncodeFacts`) proved `decode (encode i) = i`. This file closes the
other side of `Installed`'s code conjunct: the machine's `fetch32` over the
assembled byte stream (`asmBytes`) at instruction slot `j` recovers
`encode instrs[j]`, so with Phase 1 it decodes to `instrs[j]`.

Two pieces: (a) the little-endian **reassembly** — `fetch32` of the four
`insBytes` of `w` is `w`; (b) the **flatten indexing** — `asmBytes` byte
`4j + k` is `insBytes instrs[j]` byte `k`. Composed: `installed_code_of_mem`,
exactly `Installed`'s code conjunct for any memory holding `asmBytes L.instrs`
at `codeBase` (given every emitted instruction is `WF`).
-/

open LowIR Rv64i
open LowIR.Prog (dataSegment Env FunDef Name)
open LowIR.Compile (userOff)

namespace LowIR.ProgSim.AsmFacts

open EncodeFacts (WF decode_encode)

/-! ## §1 Little-endian reassembly. -/

/-- `fetch32`'s little-endian recombination of the four bytes of a 32-bit word
    is that word. -/
theorem fetch32_reassemble (w : BitVec 32) :
    (w.setWidth 8).setWidth 32 ||| ((w >>> 8).setWidth 8).setWidth 32 <<< 8
    ||| ((w >>> 16).setWidth 8).setWidth 32 <<< 16
    ||| ((w >>> 24).setWidth 8).setWidth 32 <<< 24 = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
             BitVec.getLsbD_ushiftRight]
  rcases Nat.lt_or_ge i 8 with h8 | h8
  · simp only [h8, hi, show i < 16 by omega, show i < 24 by omega, decide_true, Bool.true_and,
               Bool.not_true, Bool.false_and, Bool.and_false, Bool.or_false]
  · rcases Nat.lt_or_ge i 16 with h16 | h16
    · have e : 8 + (i - 8) = i := by omega
      simp only [hi, h16, e, show i < 24 by omega, decide_true, Bool.true_and,
                 show ¬ i < 8 by omega, decide_false, Bool.not_false, Bool.not_true,
                 Bool.false_and, Bool.and_false, Bool.and_true, show i - 8 < 32 by omega,
                 show i - 8 < 8 by omega, Bool.or_false, Bool.false_or]
    · rcases Nat.lt_or_ge i 24 with h24 | h24
      · have e : 16 + (i - 16) = i := by omega
        simp only [hi, h24, e, decide_true, Bool.true_and, show ¬ i < 8 by omega,
                   show ¬ i < 16 by omega, decide_false, Bool.not_false, Bool.not_true,
                   Bool.false_and, Bool.and_false, Bool.and_true, show i - 16 < 32 by omega,
                   show i - 16 < 8 by omega, show ¬ i - 8 < 8 by omega, Bool.or_false,
                   Bool.false_or]
      · have e : 24 + (i - 24) = i := by omega
        simp only [hi, e, decide_true, Bool.true_and, show ¬ i < 8 by omega,
                   show ¬ i < 16 by omega, show ¬ i < 24 by omega, decide_false, Bool.not_false,
                   Bool.false_and, Bool.and_false, Bool.and_true, show i - 24 < 32 by omega,
                   show i - 24 < 8 by omega, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega,
                   Bool.or_false, Bool.false_or]

/-- If memory holds the four `insBytes i` at `base .. base+3`, then `fetch32`
    from `base` is `encode i`. -/
theorem fetch32_encode (m : State) (base : Word) (i : Instr)
    (h0 : m.mem base = (encode i).setWidth 8)
    (h1 : m.mem (base + 1) = ((encode i) >>> 8).setWidth 8)
    (h2 : m.mem (base + 2) = ((encode i) >>> 16).setWidth 8)
    (h3 : m.mem (base + 3) = ((encode i) >>> 24).setWidth 8) :
    fetch32 { m with pc := base } = encode i := by
  simp only [fetch32, h0, h1, h2, h3]
  exact fetch32_reassemble (encode i)

/-! ## §2 Flatten indexing: `asmBytes` byte `4j + k` is `insBytes instrs[j]` byte `k`. -/

theorem insBytes_length (i : Instr) : (insBytes i).length = 4 := rfl

/-- `asmBytes` is a flatten of length-4 blocks: byte `4j + k` (`k < 4`) is byte
    `k` of `insBytes` of the `j`-th instruction. -/
theorem asmBytes_getElem? (is : List Instr) :
    ∀ (j k : Nat), j < is.length → k < 4 →
      (asmBytes is)[4 * j + k]? = (insBytes (is.getD j .unknown))[k]? := by
  induction is with
  | nil => intro j k hj _; exact absurd hj (by simp)
  | cons i rest ih =>
    intro j k hj hk
    have hasm : asmBytes (i :: rest) = insBytes i ++ asmBytes rest := by
      simp only [asmBytes, List.map_cons, List.flatten_cons]
    rw [hasm]
    cases j with
    | zero =>
      have hlt : 4 * 0 + k < (insBytes i).length := by rw [insBytes_length]; omega
      rw [List.getElem?_append_left hlt]; simp
    | succ j' =>
      have hge : (insBytes i).length ≤ 4 * (j' + 1) + k := by rw [insBytes_length]; omega
      have he : 4 * (j' + 1) + k - (insBytes i).length = 4 * j' + k := by
        rw [insBytes_length]; omega
      rw [List.getElem?_append_right hge, he, ih j' k (by simpa using hj) hk]
      rfl

/-- Byte-level form: memory holding `asmBytes` byte `4j+k` equals the LE byte of
    `encode instrs[j]`. -/
theorem asmBytes_getD (is : List Instr) (j k : Nat) (hj : j < is.length) (hk : k < 4) :
    (asmBytes is).getD (4 * j + k) 0 = (insBytes (is.getD j .unknown)).getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, asmBytes_getElem? is j k hj hk]

theorem asmBytes_length (is : List Instr) : (asmBytes is).length = 4 * is.length := by
  induction is with
  | nil => rfl
  | cons i rest ih =>
    have : asmBytes (i :: rest) = insBytes i ++ asmBytes rest := by
      simp only [asmBytes, List.map_cons, List.flatten_cons]
    rw [this, List.length_append, insBytes_length, ih, List.length_cons]; omega

/-! ## §3 `Installed`'s code half from a memory holding `asmBytes`. -/

/-- The core Phase-2 code lemma: if `m`'s memory holds `asmBytes L.instrs` at
    `L.codeBase` and every emitted instruction is `WF`, then every instruction
    slot decodes correctly — exactly `Installed`'s code conjunct. -/
theorem installed_code_of_mem (L : Layout) (m : State)
    (hwf : ∀ i, i ∈ L.instrs → WF i)
    (hmem : ∀ n, n < (asmBytes L.instrs).length →
              m.mem (L.codeBase + BitVec.ofNat 64 n) = (asmBytes L.instrs).getD n 0)
    (j : Nat) (hj : j < L.instrs.length) :
    decode (fetch32 { m with pc := L.codeBase + BitVec.ofNat 64 (4 * j) }) = L.instrs[j]'hj := by
  have hidx : L.instrs.getD j .unknown = L.instrs[j]'hj := (List.getElem_eq_getD Instr.unknown).symm
  -- the four little-endian bytes at slot j
  have byteEq : ∀ k, k < 4 →
      m.mem (L.codeBase + BitVec.ofNat 64 (4 * j + k)) = (insBytes L.instrs[j]).getD k 0 := by
    intro k hk
    rw [hmem (4 * j + k) (by rw [asmBytes_length]; omega), asmBytes_getD L.instrs j k hj hk, hidx]
  -- address realignment: base + literal k = codeBase + ofNat 64 (4j + k)
  have hbase : ∀ k : Nat, L.codeBase + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 k
      = L.codeBase + BitVec.ofNat 64 (4 * j + k) := by
    intro k; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [fetch32_encode m (L.codeBase + BitVec.ofNat 64 (4 * j)) L.instrs[j]
        (by have := byteEq 0 (by omega); simpa using this)
        (by have := byteEq 1 (by omega)
            rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, hbase 1]; simpa using this)
        (by have := byteEq 2 (by omega)
            rw [show (2 : Word) = BitVec.ofNat 64 2 from rfl, hbase 2]; simpa using this)
        (by have := byteEq 3 (by omega)
            rw [show (3 : Word) = BitVec.ofNat 64 3 from rfl, hbase 3]; simpa using this)]
  exact decode_encode _ (hwf _ (List.getElem_mem hj))

/-- **`Installed` from a memory holding the blob.** Decoupled into the code and
    data byte hypotheses a `loadMem`-style memory supplies directly: `hcode` for
    `asmBytes L.instrs` at `codeBase`, `hdata` for `dataSegment L.data` at
    `codeBase + segStart`. -/
theorem installed_of_mem (L : Layout) (m : State)
    (hwf : ∀ i, i ∈ L.instrs → WF i)
    (hcode : ∀ n, n < (asmBytes L.instrs).length →
               m.mem (L.codeBase + BitVec.ofNat 64 n) = (asmBytes L.instrs).getD n 0)
    (hdata : ∀ i, i < (dataSegment L.data).length →
               m.mem (L.codeBase + BitVec.ofNat 64 (L.segStart + i))
                 = (dataSegment L.data).getD i 0) :
    Installed L m := by
  refine ⟨fun j hj => installed_code_of_mem L m hwf hcode j hj, fun i hi => ?_⟩
  rw [hdata i hi]; exact (List.getElem_eq_getD 0).symm

/-! ## §4 A trivial flat obligation: `pad = userPad` satisfies `hpad`. -/

/-- `userPad` (prog_sim's `pad`) satisfies the `call` case's `hpad` obligation. -/
theorem userPad_eq (env : Env) (g : Name) (gd : FunDef)
    (h : List.lookup g env = some gd) : userPad env g = userOff gd := by
  simp only [userPad, h, Option.elim]

/-! ## §5 The remaining flat obligations, discharged from `layoutOf`/the guard.

    `lower_sim_cf`/`prog_sim` take the flat compile-time hypotheses `hdat`,
    `hstackLo`, `hdbase`, `hdpos`, `halign`, `hfn` (RESUME-CALL §C4, RESUME-PROGSIM
    §Phase-2). This section closes the three that follow from `layoutOf` and the
    compiler's own data guard alone: `hdat` (clen synth range), `hstackLo` (the
    stackLo field), and `hdbase` (the data-address correspondence). `hdpos`
    (needs a blob-size bound), `halign` (codeBase alignment — a `prog_sim`
    hypothesis) and `hfn`/`hem` (the layout↔`Emitted` correspondence) are still
    owed. -/

open LowIR.Prog (Program Data dataOffsetsFrom dbaseOf dataOffsetsFrom_shift)
open LowIR.Compile (compileProgT)

/-! ### `hstackLo` — the layout's stack floor is the requested one. -/

/-- `layoutOf` copies its `stackLo` argument into the `Layout` field verbatim. -/
theorem layoutOf_stackLo {P : Program} {entry : Name} {cb slo : Word} {L : Layout}
    (h : layoutOf P entry cb slo = some L) : L.stackLo = slo := by
  unfold layoutOf at h
  cases hc : compileProgT P entry with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some t => rw [hc] at h; simp only [Option.some.injEq] at h; rw [← h]

/-! ### `hdat` — the clen data-length synth stays in the 12-bit signed range. -/

/-- A looked-up data object's length is bounded by the whole-list bound (or the
    lookup misses, giving `0`). Mathlib-free, `BEq`-agnostic: induct on the list
    rather than route through membership (no `LawfulBEq` needed). -/
theorem lookup_len_lt (data : Data) (b : Nat) (d : Name)
    (hwf : data.all (fun x => x.2.length < b)) :
    (((List.lookup d data).map (·.length)).getD 0 : Nat) < b ∨ List.lookup d data = none := by
  induction data with
  | nil => right; rfl
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hwf
    rw [List.lookup_cons]
    by_cases he : (d == hd.1) = true
    · left; simp only [he, Option.map_some, Option.getD_some]; exact of_decide_eq_true hwf.1
    · simp only [he]; exact ih hwf.2

/-- `compileProgT = some` forces the data guard (`length < 2^22`) — the tightened
    bound (Compile.lean, 2026-07-05) that keeps `clen`'s `synthConst` in range. -/
theorem compileProgT_dataBound {P : Program} {entry : Name} {t}
    (h : compileProgT P entry = some t) : P.data.all (fun d => d.2.length < 2 ^ 22) := by
  unfold compileProgT at h
  cases hg : (LowIR.Prog.wfProgram P && P.env.all (fun nf => LowIR.Compile.fnOk nf.2)
       && (List.lookup entry P.env).isSome
       && P.data.all (fun d => d.2.length < 2 ^ 22)) with
  | false => rw [hg] at h; simp at h
  | true => simp only [Bool.and_eq_true] at hg; exact hg.2

/-- **`hdat`.** For any program whose data satisfies the compiler guard, every
    object's `clen` length synthesizes within the 12-bit signed immediate window
    (`-2048 ≤ synthHi ≤ 2047`) — so `run_synth` fires. -/
theorem clen_synthOk {P : Program} (hwf : P.data.all (fun d => d.2.length < 2 ^ 22)) (d : Name) :
    -2048 ≤ synthHi (((List.lookup d P.data).map (·.length)).getD 0)
    ∧ synthHi (((List.lookup d P.data).map (·.length)).getD 0) ≤ 2047 := by
  cases h : List.lookup d P.data with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    unfold synthHi synthLo; constructor <;> omega
  | some bs =>
    have hb : (bs.length : Nat) < 2 ^ 22 := by
      rcases lookup_len_lt P.data (2 ^ 22) d hwf with hl | hn
      · rw [h] at hl; simpa using hl
      · rw [h] at hn; exact absurd hn (by simp)
    simp only [Option.map_some, Option.getD_some]
    have : ((bs.length : Nat) : Int) < 2 ^ 22 := by exact_mod_cast hb
    unfold synthHi synthLo; constructor <;> omega

/-! ### `hdbase` — the IL data base agrees with the layout's `dpos`. -/

/-- The `dpos : Name → Nat` prog_sim feeds `emitCF`: the byte offset of object
    `d` inside the blob (`segStart` + its offset within the data segment). This IS
    the compiler's `resolveOne` table `dataOffsetsFrom (pad8 codeEnd)` — matched to
    `segStart` by the (owed) layout correspondence, via `dataOffsetsFrom_shift`. -/
def dposOf (L : Layout) : Name → Nat := fun d =>
  (List.lookup d (dataOffsetsFrom L.segStart L.data)).getD 0

/-- **`hdbase`.** The IL address map `dbaseOf (codeBase + segStart)` lands each
    object at `codeBase + dposOf d`, exactly `emitCF`'s cref target. -/
theorem dbaseOf_dposOf (L : Layout) (d : Name) (a : Word)
    (h : dbaseOf (L.codeBase + BitVec.ofNat 64 L.segStart) L.data d = some a) :
    a = L.codeBase + BitVec.ofNat 64 (dposOf L d) := by
  unfold dbaseOf dposOf at *
  cases ho : List.lookup d (dataOffsetsFrom 0 L.data) with
  | none => rw [ho] at h; exact absurd h (by simp)
  | some off =>
    rw [ho] at h; simp only [Option.map_some, Option.some.injEq] at h
    have hshift : List.lookup d (dataOffsetsFrom L.segStart L.data)
        = (List.lookup d (dataOffsetsFrom 0 L.data)).map (L.segStart + ·) := by
      have := dataOffsetsFrom_shift (n := d) L.segStart 0 L.data
      simpa using this
    rw [hshift, ho]
    simp only [Option.map_some, Option.getD_some]
    rw [← h, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

end LowIR.ProgSim.AsmFacts
