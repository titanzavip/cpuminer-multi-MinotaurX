/*
 * Copyright 2011 ArtForz
 * Copyright 2011-2013 pooler
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the Free
 * Software Foundation; either version 2 of the License, or (at your option)
 * any later version.  See COPYING for more details.
 */

#include "miner.h"

#include <string.h>
#include <inttypes.h>
#include <secp256k1.h>
#ifdef _MSC_VER
#define ROTL(a, b) _rotl(a,b)
#define ROTR(a, b) _rotr(a,b)
#else
#define ROTL(a, b) (((a) << b) | ((a) >> (32 - b)))
#define ROTR(a, b) ((a >> b) | (a << (32 - b)))
#endif
static const uint32_t sha256_k[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

/* Elementary functions used by SHA256 */
#define Ch(x, y, z)     ((x & (y ^ z)) ^ z)
#define Maj(x, y, z)    ((x & (y | z)) | (y & z))
#define S0(x)           (ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22))
#define S1(x)           (ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25))
#define s0(x)           (ROTR(x, 7) ^ ROTR(x, 18) ^ (x >> 3))
#define s1(x)           (ROTR(x, 17) ^ ROTR(x, 19) ^ (x >> 10))

/* SHA256 round function */
#define RND(a, b, c, d, e, f, g, h, k) \
    do { \
        t0 = h + S1(e) + Ch(e, f, g) + k; \
        t1 = S0(a) + Maj(a, b, c); \
        d += t0; \
        h  = t0 + t1; \
        } while (0)

/* Adjusted round function for rotating state */
#define RNDr(S, W, i) \
    RND(S[(64 - i) % 8], S[(65 - i) % 8], \
        S[(66 - i) % 8], S[(67 - i) % 8], \
        S[(68 - i) % 8], S[(69 - i) % 8], \
        S[(70 - i) % 8], S[(71 - i) % 8], \
        W[i] + sha256_k[i])
// Fast byte swap
static inline uint32_t swab32(uint32_t x) {
    return ((x & 0x000000ff) << 24) |
           ((x & 0x0000ff00) << 8) |
           ((x & 0x00ff0000) >> 8) |
           ((x & 0xff000000) >> 24);
}
// Faster be32dec
static inline uint32_t be32dec(const void *pp)
{
    const uint8_t *p = (const uint8_t *)pp;
    return ((uint32_t)(p[3])      ) |
           ((uint32_t)(p[2]) <<  8) |
           ((uint32_t)(p[1]) << 16) |
           ((uint32_t)(p[0]) << 24);
}

// Faster be32enc
static inline void be32enc(void *pp, uint32_t x)
{
    uint8_t *p = (uint8_t *)pp;
    p[3] = x & 0xff;
    p[2] = (x >> 8) & 0xff;
    p[1] = (x >> 16) & 0xff;
    p[0] = (x >> 24) & 0xff;
}
static inline void sha256_transform_volatile(uint32_t *state, uint32_t *block)
{
    uint32_t* W=block; //note: block needs to be a mutable 64 int32_t
    uint32_t S[8];
    uint32_t t0, t1;
    int i;
    // Unroll loop for better performance.
    #pragma unroll
    for (i = 16; i < 64; i += 2) {
        W[i]   = s1(W[i - 2]) + W[i - 7] + s0(W[i - 15]) + W[i - 16];
        W[i+1] = s1(W[i - 1]) + W[i - 6] + s0(W[i - 14]) + W[i - 15];
    }

    /* 2. Initialize working variables. */
    memcpy(S, state, 32);

    /* 3. Mix. */
        
    #pragma unroll
    for(i=0;i<64;i++)
    {
        RNDr(S, W, i);
    }

    /* 4. Mix local working variables into global state */
    #pragma unroll
    for (i = 0; i < 8; i++)
        state[i] += S[i];
}
static inline void sha256_hash(unsigned char *hash, const unsigned char *data, int len)
{
    uint32_t _ALIGN(64) S[16];
    uint32_t _ALIGN(64) T[64];
    int i, r;

    sha256_init(S);
    
    for (r = len; r > -9; r -= 64) {
        if (r < 64)
            memset(T, 0, 64);
        memcpy(T, data + len - r, r > 64 ? 64 : (r < 0 ? 0 : r));
        if (r >= 0 && r < 64)
            ((unsigned char *)T)[r] = 0x80;
        
        #pragma unroll
        for (i = 0; i < 16; i++)
            T[i] = be32dec(T + i);

        if (r < 56)
            T[15] = 8 * len;
        
        sha256_transform_volatile(S, T);
    }

    #pragma unroll
    for (i = 0; i < 8; i++)
        be32enc((uint32_t *)hash + i, S[i]);
}
int scanhash_curvehash(int thr_id, struct work *work, uint32_t max_nonce, uint64_t *hashes_done) {
    secp256k1_context *ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN);
    secp256k1_pubkey pubkey;
    unsigned char pub[65];
    size_t publen = 65;

    uint32_t _ALIGN(128) hash[8];
    uint32_t _ALIGN(128) hash_le[8];
    uint32_t *pdata = work->data;
    uint32_t *ptarget = work->target;
    uint32_t _ALIGN(128) pdata_be[20];
    
    // Precompute
    #pragma unroll
    for (int i = 0; i < 20; i++) {
        pdata_be[i] = swab32(pdata[i]);
    }
    uint32_t first_nonce = pdata[19];
    uint32_t nonce = first_nonce;
    const uint32_t Htarg = ptarget[7];
    
    unsigned char temp_pub[65*8];
    #pragma unroll
    for(int round = 0; round < 8;round++)
    {
        sha256_hash(temp_pub+(65*round),temp_pub+(65*(round>0?round-1:0)),round>0?65:80);
        secp256k1_ec_pubkey_create(ctx, &pubkey, temp_pub+(65*round));
        secp256k1_ec_pubkey_serialize(ctx, temp_pub+(65*round), &publen, &pubkey, SECP256K1_EC_UNCOMPRESSED);
    }
    do {
        pdata[19] = nonce;
        pdata_be[19] = swab32(pdata[19]);
        memcpy(temp_pub, pdata_be, 80);
        for (int round = 0; round < 8; round++) {
            sha256_hash(temp_pub+(65*round),temp_pub+(65*(round>0?round-1:0)),round>0?65:80);
            
        }
        if (temp_pub[64*7+63] < Htarg) {
            if (fulltest((uint32_t *)temp_pub+(64*7), ptarget)) {
                work_set_target_ratio(work, (uint32_t *)temp_pub+(64*7));
                pdata[19] = nonce;
                *hashes_done = pdata[19] - first_nonce;
                secp256k1_context_destroy(ctx);
                return 1;
            }
        }
        nonce++;
    } while (nonce < max_nonce && !work_restart[thr_id].restart);
    *hashes_done = pdata[19] - first_nonce;
    secp256k1_context_destroy(ctx);
    return 0;
}
