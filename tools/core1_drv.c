// Test driver for the ASSEMBLY core1 (bare/core1.s), run under qemu-riscv64.
// Same protocol as hex1_drv: argv[1] = out_cap, input on stdin, output bytes
// on stdout, status as exit code. Build:
//   riscv64-linux-gnu-gcc -O2 -static -o tools/core1_drv tools/core1_drv.c bare/core1.s
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

// RISC-V LP64 psABI: a struct of two longs is returned in a0/a1.
typedef struct { unsigned long status; unsigned long out_len; } Core1Ret;
extern Core1Ret core1(const char *in_ptr, unsigned long in_len,
                      char *out_ptr, unsigned long out_cap,
                      int64_t *lbl_ptr);

int main(int argc, char **argv) {
    if (argc < 2) { return 100; }
    size_t cap = strtoull(argv[1], NULL, 10);
    static char in_buf[1 << 20];
    size_t in_len = fread(in_buf, 1, sizeof(in_buf), stdin);
    char *out = malloc(cap ? cap : 1);
    static int64_t labels[256]; // core1 initializes; garbage is fine too
    if (out == NULL) { return 101; }
    Core1Ret r = core1(in_buf, in_len, out, cap, labels);
    fwrite(out, 1, r.out_len, stdout);
    return (int)r.status;
}
