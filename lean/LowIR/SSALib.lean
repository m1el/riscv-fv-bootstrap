/-
  LowIR.SSA.Lib — strlen and hex0 ported from `LowIR.ProgLib` onto the SSA
  experiment IR (docs/LOWIR-SSA-EXPERIMENT.md §port). What changes shape:

  • The error cascade dissolves. Prog's `err code = (x14 := code); ret` +
    "status register x14, initialized 0, read at the boundary" becomes a
    literal valued return `ret [.const code, .reg n]` at each failure site,
    and the success exit is the loop guard's `defaultBody` returning
    `[.const 0, .reg n]`. Registers x14 (status), x15 (comment-guard flag)
    and x16 (the constant 1) disappear from hex0 entirely.

  • `pnib` (nibble decode, a 5-leaf decision tree that in Prog ASSIGNS its
    dst on every leaf and falls through) becomes a value-producing `ife`:
    each leaf `brk k [value]` to the outs-carrying root, sentinel leaves are
    `.const 255` — no register holds them.

  • `skipComment` (Prog: compute a guard bit into x15 via `cgGuard`, loop on
    `x15 ≥u 1`) becomes an always-true inner loop whose exits `cont 1`
    DIRECTLY to the outer scan loop — the cross-loop continue-with-values is
    the tail call the design wanted; no flag register, no re-computed guard.

  • The cost, honestly: Prog reuses scratch x30/x31 at every site; SSA needs
    a fresh name per textual site, so the helpers take their scratch
    registers as parameters and the function allocates ~20 extra names.
    Every dispatch arm must end in an explicit `cont`/`ret` (no fallthrough).

  Both functions are validated the same way as ProgLib: strlen on the string
  battery, hex0 against `Hex0.coreSpec` on the full Ctrl battery
  (`native_decide`). Results are read from the returned VALUE LIST — no
  register-reading convention at the boundary.
-/
import LowIR.SSA
import LowIR.CtrlHex0        -- Hex0.coreSpec (via Hex0.Spec) + the hex0 battery

namespace LowIR.SSA.Lib

open Rv64i (Word Byte)

/-- `seqs` without a trailing `.skip`: the last statement is the tail, so a
    `.never`-typed ending (ret / an all-exits-return loop) is not followed by
    dead code (which `check` rejects). -/
def seqs1 : List Stmt → Stmt
  | []        => .skip
  | [s]       => s
  | s :: rest => .seq s (seqs1 rest)

def lit (r v : Nat) : Stmt := .addi r 0 (BitVec.ofNat 12 v)

/-! ## strlen(p=10) → (n)

    Loop-carried args: cursor + the byte AT the cursor (loaded before each
    `cont`, seeded before the loop — the guard itself cannot load). The
    guard-exit `dflt` computes the length from the final cursor: the
    loop-carried result survives the guard exit by construction. -/

def strlenS : FunDef :=
  { rvc := 1, params := [10], frameSize := 0, frameReg := 3
    body := seqs1
      [ .lbu 5 10 0,                                   -- b0 := mem[p]
        lit 16 1,
        .«while» [12] [.reg 10, .reg 5] [6, 7] .geu 7 16   -- (cur, b); while b ≥u 1
          (.seq (.addi 8 6 1) <| .seq (.lbu 9 8 0)
            (.cont 0 [.reg 8, .reg 9]))
          (.seq (.sub 13 6 10) (.brk 0 [.reg 13])),    -- n := cur − p
        .ret [.reg 12] ] }

/-! ## hex0(in=10, len=11, out=12, cap=13) → (status, outlen)

    Constant registers (defined once, before the loop — SSA-legal):
    17='7'+8=55  18=';'  19=255  20='0'  21='9'  22='A'  23='F'
    24='\n'  25=' '  26='_'  27='#'.
    Loop args: 5 = in_idx (i), 6 = out_idx (n). Every failure site returns
    `[code, n]` directly; the guard-false `dflt` returns `[0, n]`. -/

/-- Failure exit: status + current outlen, straight out of the function. -/
def err (code : Nat) : Stmt := .ret [.const (BitVec.ofNat 64 code), .reg 6]

/-- Nibble decode as a value-producing `ife`: dst := decode src, 255 = bad.
    `t1`/`t2` are the per-instantiation subtraction scratches. -/
def pnibS (dst t1 t2 src : Reg) : Stmt :=
  .ife .geu src 20 [dst]
    (.ife .geu 21 src []
      (.seq (.sub t1 src 20) (.brk 1 [.reg t1]))       -- '0'..'9' → src−48
      (.ife .geu src 22 []
        (.ife .geu 23 src []
          (.seq (.sub t2 src 17) (.brk 3 [.reg t2]))   -- 'A'..'F' → src−55
          (.brk 3 [.const 255]))
        (.brk 2 [.const 255])))
    (.brk 0 [.const 255])

/-- Skip to the next '\n' (or EOF) starting at `i1`. An always-true inner
    loop; both exits `cont 1 [pos, n]` — continuing the OUTER scan loop
    directly (the '\n' itself is left for the outer loop to consume as
    whitespace, exactly Prog's behavior). `j j1 a b` per-instantiation. -/
def skipCommentS (i1 j j1 a b : Reg) : Stmt :=
  .«while» [] [.reg i1] [j] .geu 0 0
    (.ife .lt j 11 []
      (.seq (.add a 10 j) <| .seq (.lbu b a 0)
        (.ife .eq b 24 []
          (.cont 1 [.reg j, .reg 6])                   -- next is '\n': resume scan
          (.seq (.addi j1 j 1) (.cont 0 [.reg j1]))))  -- still in comment
      (.cont 1 [.reg j, .reg 6]))                      -- EOF: outer guard will fail
    (.cont 1 [.reg j, .reg 6])                         -- unreachable (guard is true)

/-- `<BYTE>`: two nibbles with Prog's exact guard order; ends by continuing
    the scan with (i+2 input chars consumed, n+1 bytes emitted). Uses the
    outer-body names 41 = i+1 and 7 = first char. -/
def hexPathS : Stmt := seqs1
  [ pnibS 28 54 55 7,
    .ife .eq 28 19 [] (err 5) .skip,                   -- Unknown
    .ife .geu 41 11 [] (err 4) .skip,                  -- OddEnd (input exhausted)
    .add 56 10 41, .lbu 57 56 0, .addi 58 41 1,        -- read 2nd char
    .ife .eq 57 24 [] (err 3) .skip,                   -- Split: '\n'
    .ife .eq 57 25 [] (err 3) .skip,                   --        ' '
    .ife .eq 57 26 [] (err 3) .skip,                   --        '_'
    .ife .eq 57 27 [] (err 3) .skip,                   --        '#'
    .ife .eq 57 18 [] (err 3) .skip,                   --        ';'
    pnibS 29 59 60 57,
    .ife .eq 29 19 [] (err 5) .skip,                   -- Unknown (2nd nibble)
    .ife .geu 6 13 [] (err 2) .skip,                   -- OutputShort
    .slli 50 28 4, .orr 51 50 29,
    .add 52 12 6, .sb 52 51 0, .addi 53 6 1,
    .cont 0 [.reg 58, .reg 53] ]

def hex0BodyS : Stmt :=
  .seq (.add 40 10 5) <| .seq (.lbu 7 40 0) <| .seq (.addi 41 5 1) <|
  .ife .eq 7 27 [] (skipCommentS 41 42 43 44 45) <|
  .ife .eq 7 18 [] (skipCommentS 41 46 47 48 49) <|
  .ife .eq 7 24 [] (.cont 0 [.reg 41, .reg 6]) <|
  .ife .eq 7 25 [] (.cont 0 [.reg 41, .reg 6]) <|
  .ife .eq 7 26 [] (.cont 0 [.reg 41, .reg 6]) <|
  hexPathS

def hex0S : FunDef :=
  { rvc := 2, params := [10, 11, 12, 13], frameSize := 0, frameReg := 3
    body := seqs1
      [ lit 17 55, lit 18 59, lit 19 255, lit 20 48, lit 21 57, lit 22 65,
        lit 23 70, lit 24 10, lit 25 32, lit 26 95, lit 27 35,
        .«while» [] [.const 0, .const 0] [5, 6] .lt 5 11
          hex0BodyS
          (.ret [.const 0, .reg 6]) ] }               -- success: guard-false exit

def libEnvS : Env := [("strlen", strlenS), ("hex0", hex0S)]

-- the port passes the SSA checker (def-once census + use/arity/never typing)
#guard wfEnv libEnvS

/-! ## Validation against the specs (same regime as ProgLib) -/

def inBase  : Word := 0x1000
def outBase : Word := 0x4000
def SP0     : Word := 0x80000

def sbytes (s : String) : List Nat := s.toList.map Char.toNat
def asBytes (l : List Nat) : List Byte := l.map (BitVec.ofNat 8)

def memIn (inp : List Byte) : Word → Byte := fun a =>
  let ia := (a - inBase).toNat
  if ia < inp.length then (inp[ia]?).getD 0 else 0

/-- Run hex0; (status, out bytes, len) — status/len from the VALUE list. -/
def hexRunS (inp : List Nat) (cap fuel : Nat) : Nat × List Nat × Nat :=
  match run libEnvS 0 fuel "hex0"
          [inBase, BitVec.ofNat 64 inp.length, outBase, BitVec.ofNat 64 cap]
          (memIn (asBytes inp)) SP0 with
  | some (s, [status, outlen]) =>
      (status.toNat,
       (List.range outlen.toNat).map
         (fun i => (s.mem (outBase + BitVec.ofNat 64 i)).toNat),
       outlen.toNat)
  | _ => (255, [], 0)

/-- SSA hex0 matches `Hex0.coreSpec` on the full Ctrl battery. -/
theorem hex0S_matches_spec :
    LowIR.Ctrl.Hex0.battery.all (fun tc =>
      hexRunS tc.1 tc.2 100000 == Hex0.coreSpec tc.1 tc.2) = true := by
  native_decide

/-- SSA strlen over the ProgLib string battery. -/
theorem strlenS_ok :
    [("", 0), ("x", 1), ("Hello", 5), ("Hi!", 3)].all (fun tc =>
      (match run libEnvS 0 1000 "strlen" [inBase]
               (memIn (asBytes (sbytes tc.1 ++ [0]))) SP0 with
       | some (_, [n]) => n.toNat
       | _             => 999)
      == tc.2) = true := by
  native_decide

end LowIR.SSA.Lib
