/- LowIR rung — the structured IL (Core → Ctrl → Prog), the verified compiler
   to RV64I, the combined function library (`LowIR.Lib`), and the compile_sim
   proof campaign (`LowIR.ProgSim`). Programs live under `LowIR/{Hex0,Strlen,
   Strtoull}/`. -/
import LowIR.Core
import LowIR.Ctrl
import LowIR.Prog
import LowIR.Compile
import LowIR.Dump
import LowIR.Lib
import LowIR.CompileTests
