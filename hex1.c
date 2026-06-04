// hex1 -- hex0 plus single-character labels and i32 relative references.
// Spec: HEX1.md. Reference implementation; the proof target is bare/core1.s.
//
// Grammar additions over hex0:
//   :<byte>  define label <byte> at the current output position (no repeats)
//   %<byte>  emit i32 LE: label_pos - (field_pos + 4)   (end-relative, rel32)
// The byte after ':' or '%' is consumed unconditionally (any of 256 values).
// ':' and '%' join the stop-character set.
//
// Two passes: scan (grammar + capacity + label collection), then emit
// (bytes + reference resolution). Forward references allowed.
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#define MIN_SIZE 4096

typedef enum Error_e {
    ErrOk = 0,
    ErrOutOfMemory = 1,
    ErrOutputShort = 2,
    ErrSplitNibble = 3,
    ErrTrailingNibble = 4,
    ErrUnknownChar = 5,
    ErrDuplicateLabel = 6,
    ErrUndefinedLabel = 7,
    ErrTrailingToken = 8,
    ErrBadNibble = 255,
} Error;

typedef struct ByteVec_s {
    char *buf;
    size_t cap;
    size_t len;
} ByteVec;

static Error ensure_push(ByteVec *vec, size_t el_size, size_t extra) {
    if (vec->len + extra < vec->len) {
        return ErrOutOfMemory;
    }
    if (extra == 0) { return ErrOk; }
    while (vec->len + extra > vec->cap) {
        if ((~(size_t)0) / 2 < vec->cap) {
            return ErrOutOfMemory;
        }
        vec->cap = vec->cap == 0 ? 1 : vec->cap;
        vec->cap *= 2;
        // multiply overflow
        if ((~(size_t)0) / el_size < vec->cap) {
            return ErrOutOfMemory;
        }
        vec->buf = realloc(vec->buf, el_size * vec->cap);
        if (vec->buf == NULL) {
            vec->cap = 0;
            return ErrOutOfMemory;
        }
    }
    return ErrOk;
}

static int slurp(FILE *fd, ByteVec *out) {
    ByteVec rv = {malloc(MIN_SIZE), MIN_SIZE, 0};
    size_t bread = 1;
    int err = 0;
    if (rv.buf == NULL) {
        rv.cap = 0;
        err = ErrOutOfMemory;
        bread = 0;
    }
    while (bread > 0) {
        if (ensure_push(&rv, 1, 1) != 0) {
            err = ErrOutOfMemory;
            break;
        }
        bread = fread(&rv.buf[rv.len], 1, rv.cap - rv.len, fd);
        rv.len += bread;
    }
    *out = rv;
    if (err == 0) {
        err = ferror(fd);
    }
    return err;
}

char parse_nibble(char in) {
    if (in >= '0' && in <= '9') {
        return in - '0';
    }
    if (in >= 'A' && in <= 'F') {
        return in - ('A' - 10);
    }
    return (char)ErrBadNibble;
}

// Pass 1: tokenize, check grammar and capacity, collect label positions.
// labels[c] = output position of label c, or -1 if (not yet) defined.
// Emits nothing. Maintains the invariant out_idx <= out_cap.
static
Error scan(const char *in, size_t in_len, size_t out_cap, int64_t *labels) {
    size_t in_idx = 0;
    size_t out_idx = 0;

    while (in_idx < in_len) {
        char chr = in[in_idx];
        in_idx += 1;
        // skip single line comments after # or ;
        if (chr == '#' || chr == ';') {
            while (in_idx < in_len && in[in_idx] != '\n') {
                in_idx += 1;
            }
            continue;
        }
        if (chr == '\n' || chr == ' ' || chr == '_') {
            continue;
        }
        if (chr == ':') {
            if (in_idx >= in_len) {
                return ErrTrailingToken;
            }
            uint8_t lbl = (uint8_t)in[in_idx];
            in_idx += 1;
            if (labels[lbl] >= 0) {
                return ErrDuplicateLabel;
            }
            labels[lbl] = (int64_t)out_idx;
            continue;
        }
        if (chr == '%') {
            if (in_idx >= in_len) {
                return ErrTrailingToken;
            }
            in_idx += 1; // label byte; resolution is checked in pass 2
            if (out_cap - out_idx < 4) {
                return ErrOutputShort;
            }
            out_idx += 4;
            continue;
        }
        char high = parse_nibble(chr);
        if ((uint8_t)high == ErrBadNibble) {
            return ErrUnknownChar;
        }
        if (in_idx >= in_len) {
            return ErrTrailingNibble;
        }
        chr = in[in_idx];
        in_idx += 1;
        if (chr == '\n' || chr == ' ' || chr == '_' || chr == '#' ||
            chr == ';' || chr == ':' || chr == '%') {
            return ErrSplitNibble;
        }
        char low = parse_nibble(chr);
        if ((uint8_t)low == ErrBadNibble) {
            return ErrUnknownChar;
        }
        if (out_idx >= out_cap) {
            return ErrOutputShort;
        }
        out_idx += 1;
    }
    return ErrOk;
}

// Pass 2: emit bytes and resolve references. Grammar and capacity were
// validated by scan, so the only possible error is an undefined label.
// On ErrUndefinedLabel, *out_len = position of the failing field.
static
Error emit(const char *in, size_t in_len, char *out, size_t *out_len,
           const int64_t *labels) {
    size_t in_idx = 0;
    size_t out_idx = 0;

    while (in_idx < in_len) {
        char chr = in[in_idx];
        in_idx += 1;
        if (chr == '#' || chr == ';') {
            while (in_idx < in_len && in[in_idx] != '\n') {
                in_idx += 1;
            }
            continue;
        }
        if (chr == '\n' || chr == ' ' || chr == '_') {
            continue;
        }
        if (chr == ':') {
            in_idx += 1; // label byte; recorded in pass 1
            continue;
        }
        if (chr == '%') {
            uint8_t lbl = (uint8_t)in[in_idx];
            in_idx += 1;
            if (labels[lbl] < 0) {
                *out_len = out_idx;
                return ErrUndefinedLabel;
            }
            // off = label_pos - (field_pos + 4), truncated mod 2^32, LE
            uint32_t off = (uint32_t)((uint64_t)labels[lbl]
                                      - ((uint64_t)out_idx + 4));
            out[out_idx] = (char)(off & 0xff);
            out[out_idx + 1] = (char)((off >> 8) & 0xff);
            out[out_idx + 2] = (char)((off >> 16) & 0xff);
            out[out_idx + 3] = (char)((off >> 24) & 0xff);
            out_idx += 4;
            continue;
        }
        char high = parse_nibble(chr);
        chr = in[in_idx];
        in_idx += 1;
        char low = parse_nibble(chr);
        out[out_idx] = (high << 4) | low;
        out_idx += 1;
    }
    *out_len = out_idx;
    return ErrOk;
}

// The pure top-level function; mirrors the bare/core1.s contract.
// On a scan (phase-1) error, *out_len = 0 and nothing is written.
Error unhex1(const char *in, size_t in_len, char *out, size_t out_cap,
             size_t *out_len) {
    int64_t labels[256];
    for (size_t ii = 0; ii < 256; ii += 1) {
        labels[ii] = -1;
    }
    *out_len = 0;
    Error err = scan(in, in_len, out_cap, labels);
    if (err != ErrOk) {
        return err;
    }
    return emit(in, in_len, out, out_len, labels);
}

int main(int argc, char **argv) {
    (void)argc;
    (void)argv;
    int err = 0;
    ByteVec input = {0};
    err = slurp(stdin, &input);
    if (err != 0) { return err; }

    // Each output byte needs >= 2 input chars ('%c' -> 4 bytes), so
    // out_len <= 2 * in_len and ErrOutputShort is unreachable from here.
    ByteVec output = {malloc(MIN_SIZE), MIN_SIZE, 0};
    if (output.buf == NULL || ensure_push(&output, 1, input.len * 2) != 0) {
        return ErrOutOfMemory;
    }
    size_t out_len = 0;
    err = unhex1(input.buf, input.len, output.buf, output.cap, &out_len);
    fwrite(output.buf, 1, out_len, stdout);
    if (err != 0) {
        fprintf(stderr, "hex1: error %d\n", err);
    }
    return err;
}
