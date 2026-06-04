// Test driver for hex1's pure function: argv[1] = out_cap, input on stdin,
// output bytes on stdout, status as exit code.
#define main hex1_main
#include "../hex1.c"
#undef main

int main(int argc, char **argv) {
    if (argc < 2) { return 100; }
    size_t cap = strtoull(argv[1], NULL, 10);
    ByteVec input = {0};
    if (slurp(stdin, &input) != 0) { return 101; }
    char *out = malloc(cap ? cap : 1);
    if (out == NULL) { return 101; }
    size_t out_len = 0;
    Error err = unhex1(input.buf, input.len, out, cap, &out_len);
    fwrite(out, 1, out_len, stdout);
    return err;
}
