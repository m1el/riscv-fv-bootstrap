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

static
Error unhex(char *in, size_t in_len, char *out, size_t *out_len) {
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
        char high = parse_nibble(chr);
        if ((uint8_t)high == ErrBadNibble) {
            return ErrUnknownChar;
        }
        if (in_idx >= in_len) {
            return ErrTrailingNibble;
        }
        chr = in[in_idx];
        in_idx += 1;
        if (chr == '\n' || chr == ' ' || chr == '_' || chr == '#' || chr == ';') {
            return ErrSplitNibble;
        }
        char low = parse_nibble(chr);
        if ((uint8_t)low == ErrBadNibble) {
            return ErrUnknownChar;
        }
        if (out_idx >= *out_len) {
            return ErrOutputShort;
        }
        out[out_idx] = (high << 4) | low;
        out_idx += 1;
    }
    *out_len = out_idx;
    return ErrOk;
}

Error hex(char *in, size_t in_len, char *out, size_t *out_len) {
    // ii, pos < 48 < size_t
    char buf[48];
    const char *alphabet = "0123456789ABCDEF";
    size_t out_pos = 0;
    for (size_t ii = 0; ii < in_len; ii += 1) {
        size_t val = (uint8_t)in[ii];
        size_t pos = (ii & 0x0f) * 3;
        buf[pos] = alphabet[val >> 4];
        buf[pos + 1] = alphabet[val & 0x0f];
        buf[pos + 2] = ' ';
        if (((ii & 0x0f) == 0x0f) || ii + 1 >= in_len) {
            buf[pos + 2] = '\n';
            size_t extra = pos + 3;
            if (out_pos + extra < out_pos || out_pos + extra > *out_len) {
                return ErrOutputShort;
            }
            memcpy(out + out_pos, &buf[0], extra);
            out_pos += extra;
        }
    }
    return ErrOk;
}

size_t estimate_hex(size_t bytes) {
    size_t rv = bytes * 2;
    rv = ((rv + 31) / 32) * 48;
    return rv;
}

int main(int argc, char **argv) {
    (void)argc;
    (void)argv;
    int err = 0;
    ByteVec input = {0};
    err = slurp(stdin, &input);
    if (err != 0) { return err; }

    ByteVec output = {malloc(MIN_SIZE), MIN_SIZE, 0};
    ensure_push(&output, 1, input.len / 2);
    output.len = output.cap;
    unhex(input.buf, input.len, output.buf, &output.len);
    fwrite(output.buf, 1, output.len, stdout);

    ByteVec roundtrip = {malloc(MIN_SIZE), MIN_SIZE, 0};
    ensure_push(&roundtrip, 1, estimate_hex(output.len));
    roundtrip.len = roundtrip.cap;
    hex(output.buf, output.len, roundtrip.buf, &roundtrip.len);
    fwrite(roundtrip.buf, 1, roundtrip.len, stdout);
       
    return 0;
}

