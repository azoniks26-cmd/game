#ifdef __ANDROID__
#include <jni.h>
#include <android/log.h>
#include <android/native_window.h>
#include <android/native_window_jni.h>
#include <EGL/egl.h>
#include <EGL/eglext.h>
#include <GLES3/gl3.h>
#include <android/asset_manager.h>
#include <android/asset_manager_jni.h>
#endif
#include <zlib.h>
#include <sys/stat.h>
#ifdef __ANDROID__
#include <sys/system_properties.h>
#include <sys/prctl.h>
#endif
#include <arpa/inet.h>
#include <unistd.h>
#include <fcntl.h>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <string>
#include <vector>
#include <unordered_map>
#include <memory>
#include <mutex>
#include <atomic>
#include <thread>
#include <chrono>
#include <functional>
#include <algorithm>
#include <cctype>
#include <dirent.h>

#define WA_LOG(...) __android_log_print(ANDROID_LOG_WARN, "WARARENA", __VA_ARGS__)

#ifndef WA_DESKTOP_TEST
#define WA_DESKTOP_TEST 0
#endif

namespace wa {

using u8 = uint8_t;
using u16 = uint16_t;
using i16 = int16_t;
using i8 = int8_t;
using u32 = uint32_t;
using u64 = uint64_t;
using i32 = int32_t;
using i64 = int64_t;

static void secure_wipe(void* p, size_t n) {
    volatile u8* v = (volatile u8*)p;
    while (n--) *v++ = 0;
}

struct Bytes {
    std::vector<u8> d;
    size_t size() const { return d.size(); }
    u8* data() { return d.data(); }
    const u8* data() const { return d.data(); }
    void clear() { std::vector<u8>().swap(d); }
};

namespace crypt {

static inline u32 ror32(u32 x, int n) { return (x >> n) | (x << (32 - n)); }
static inline u64 ror64(u64 x, int n) { return (x >> n) | (x << (64 - n)); }

struct Sha256Ctx {
    u32 h[8];
    u64 len;
    u8 buf[64];
    size_t bl;
};

static const u32 K256[64] = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};

static void sha256_init(Sha256Ctx& c) {
    c.h[0]=0x6a09e667;c.h[1]=0xbb67ae85;c.h[2]=0x3c6ef372;c.h[3]=0xa54ff53a;
    c.h[4]=0x510e527f;c.h[5]=0x9b05688c;c.h[6]=0x1f83d9ab;c.h[7]=0x5be0cd19;
    c.len=0;c.bl=0;
}

static void sha256_block(Sha256Ctx& c, const u8* p) {
    u32 w[64];
    for (int i = 0; i < 16; i++) w[i] = (u32(p[i*4])<<24)|(u32(p[i*4+1])<<16)|(u32(p[i*4+2])<<8)|p[i*4+3];
    for (int i = 16; i < 64; i++) {
        u32 s0 = ror32(w[i-15],7) ^ ror32(w[i-15],18) ^ (w[i-15]>>3);
        u32 s1 = ror32(w[i-2],17) ^ ror32(w[i-2],19) ^ (w[i-2]>>10);
        w[i] = w[i-16] + s0 + w[i-7] + s1;
    }
    u32 a=c.h[0],b=c.h[1],cc=c.h[2],d=c.h[3],e=c.h[4],f=c.h[5],g=c.h[6],h=c.h[7];
    for (int i = 0; i < 64; i++) {
        u32 S1 = ror32(e,6)^ror32(e,11)^ror32(e,25);
        u32 ch = (e&f)^(~e&g);
        u32 t1 = h + S1 + ch + K256[i] + w[i];
        u32 S0 = ror32(a,2)^ror32(a,13)^ror32(a,22);
        u32 mj = (a&b)^(a&cc)^(b&cc);
        u32 t2 = S0 + mj;
        h=g;g=f;f=e;e=d+t1;d=cc;cc=b;b=a;a=t1+t2;
    }
    c.h[0]+=a;c.h[1]+=b;c.h[2]+=cc;c.h[3]+=d;c.h[4]+=e;c.h[5]+=f;c.h[6]+=g;c.h[7]+=h;
}

static void sha256_update(Sha256Ctx& c, const u8* p, size_t n) {
    c.len += n;
    while (n > 0) {
        size_t take = std::min(n, size_t(64) - c.bl);
        memcpy(c.buf + c.bl, p, take);
        c.bl += take; p += take; n -= take;
        if (c.bl == 64) { sha256_block(c, c.buf); c.bl = 0; }
    }
}

static void sha256_final(Sha256Ctx& c, u8 out[32]) {
    u64 bits = c.len * 8;
    u8 pad = 0x80;
    u8 z = 0;
    u8 tmp[72];
    memset(tmp, 0, 72);
    size_t bl = c.bl;
    memcpy(tmp, c.buf, bl);
    tmp[bl++] = 0x80;
    if (bl > 56) {
        while (bl < 64) tmp[bl++] = 0;
        sha256_block(c, tmp);
        memset(tmp, 0, 72);
        bl = 0;
    }
    while (bl < 56) tmp[bl++] = 0;
    for (int i = 0; i < 8; i++) tmp[bl + i] = u8(bits >> (56 - i*8));
    sha256_block(c, tmp);
    for (int i = 0; i < 8; i++) {
        out[i*4] = u8(c.h[i]>>24); out[i*4+1] = u8(c.h[i]>>16);
        out[i*4+2] = u8(c.h[i]>>8); out[i*4+3] = u8(c.h[i]);
    }
}

static void sha256(const u8* p, size_t n, u8 out[32]) {
    Sha256Ctx c; sha256_init(c); sha256_update(c, p, n); sha256_final(c, out);
}

struct Sha512Ctx {
    u64 h[8];
    u64 len;
    u8 buf[128];
    size_t bl;
};

static const u64 K512[80] = {
    0x428a2f98d728ae22ULL,0x7137449123ef65cdULL,0xb5c0fbcfec4d3b2fULL,0xe9b5dba58189dbbcULL,
    0x3956c25bf348b538ULL,0x59f111f1b605d019ULL,0x923f82a4af194f9bULL,0xab1c5ed5da6d8118ULL,
    0xd807aa98a3030242ULL,0x12835b0145706fbeULL,0x243185be4ee4b28cULL,0x550c7dc3d5ffb4e2ULL,
    0x72be5d74f27b896fULL,0x80deb1fe3b1696b1ULL,0x9bdc06a725c71235ULL,0xc19bf174cf692694ULL,
    0xe49b69c19ef14ad2ULL,0xefbe4786384f25e3ULL,0x0fc19dc68b8cd5b5ULL,0x240ca1cc77ac9c65ULL,
    0x2de92c6f592b0275ULL,0x4a7484aa6ea6e483ULL,0x5cb0a9dcbd41fbd4ULL,0x76f988da831153b5ULL,
    0x983e5152ee66dfabULL,0xa831c66d2db43210ULL,0xb00327c898fb213fULL,0xbf597fc7beef0ee4ULL,
    0xc6e00bf33da88fc2ULL,0xd5a79147930aa725ULL,0x06ca6351e003826fULL,0x142929670a0e6e70ULL,
    0x27b70a8546d22ffcULL,0x2e1b21385c26c926ULL,0x4d2c6dfc5ac42aedULL,0x53380d139d95b3dfULL,
    0x650a73548baf63deULL,0x766a0abb3c77b2a8ULL,0x81c2c92e47edaee6ULL,0x92722c851482353bULL,
    0xa2bfe8a14cf10364ULL,0xa81a664bbc423001ULL,0xc24b8b70d0f89791ULL,0xc76c51a30654be30ULL,
    0xd192e819d6ef5218ULL,0xd69906245565a910ULL,0xf40e35855771202aULL,0x106aa07032bbd1b8ULL,
    0x19a4c116b8d2d0c8ULL,0x1e376c085141ab53ULL,0x2748774cdf8eeb99ULL,0x34b0bcb5e19b48a8ULL,
    0x391c0cb3c5c95a63ULL,0x4ed8aa4ae3418acbULL,0x5b9cca4f7763e373ULL,0x682e6ff3d6b2b8a3ULL,
    0x748f82ee5defb2fcULL,0x78a5636f43172f60ULL,0x84c87814a1f0ab72ULL,0x8cc702081a6439ecULL,
    0x90befffa23631e28ULL,0xa4506cebde82bde9ULL,0xbef9a3f7b2c67915ULL,0xc67178f2e372532bULL,
    0xca273eceea26619cULL,0xd186b8c721c0c207ULL,0xeada7dd6cde0eb1eULL,0xf57d4f7fee6ed178ULL,
    0x06f067aa72176fbaULL,0x0a637dc5a2c898a6ULL,0x113f9804bef90daeULL,0x1b710b35131c471bULL,
    0x28db77f523047d84ULL,0x32caab7b40c72493ULL,0x3c9ebe0a15c9bebcULL,0x431d67c49c100d4cULL,
    0x4cc5d4becb3e42b6ULL,0x597f299cfc657e2aULL,0x5fcb6fab3ad6faecULL,0x6c44198c4a475817ULL
};

static void sha512_init(Sha512Ctx& c) {
    c.h[0]=0x6a09e667f3bcc908ULL;c.h[1]=0xbb67ae8584caa73bULL;c.h[2]=0x3c6ef372fe94f82bULL;c.h[3]=0xa54ff53a5f1d36f1ULL;
    c.h[4]=0x510e527fade682d1ULL;c.h[5]=0x9b05688c2b3e6c1fULL;c.h[6]=0x1f83d9abfb41bd6bULL;c.h[7]=0x5be0cd19137e2179ULL;
    c.len=0;c.bl=0;
}

static void sha512_block(Sha512Ctx& c, const u8* p) {
    u64 w[80];
    for (int i = 0; i < 16; i++) {
        w[i] = 0;
        for (int j = 0; j < 8; j++) w[i] = (w[i]<<8) | p[i*8+j];
    }
    for (int i = 16; i < 80; i++) {
        u64 s0 = ror64(w[i-15],1) ^ ror64(w[i-15],8) ^ (w[i-15]>>7);
        u64 s1 = ror64(w[i-2],19) ^ ror64(w[i-2],61) ^ (w[i-2]>>6);
        w[i] = w[i-16] + s0 + w[i-7] + s1;
    }
    u64 a=c.h[0],b=c.h[1],cc=c.h[2],d=c.h[3],e=c.h[4],f=c.h[5],g=c.h[6],h=c.h[7];
    for (int i = 0; i < 80; i++) {
        u64 S1 = ror64(e,14)^ror64(e,18)^ror64(e,41);
        u64 ch = (e&f)^(~e&g);
        u64 t1 = h + S1 + ch + K512[i] + w[i];
        u64 S0 = ror64(a,28)^ror64(a,34)^ror64(a,39);
        u64 mj = (a&b)^(a&cc)^(b&cc);
        u64 t2 = S0 + mj;
        h=g;g=f;f=e;e=d+t1;d=cc;cc=b;b=a;a=t1+t2;
    }
    c.h[0]+=a;c.h[1]+=b;c.h[2]+=cc;c.h[3]+=d;c.h[4]+=e;c.h[5]+=f;c.h[6]+=g;c.h[7]+=h;
}

static void sha512_update(Sha512Ctx& c, const u8* p, size_t n) {
    c.len += n;
    while (n > 0) {
        size_t take = std::min(n, size_t(128) - c.bl);
        memcpy(c.buf + c.bl, p, take);
        c.bl += take; p += take; n -= take;
        if (c.bl == 128) { sha512_block(c, c.buf); c.bl = 0; }
    }
}

static void sha512_final(Sha512Ctx& c, u8 out[64]) {
    u64 bits = c.len * 8;
    u8 tmp[256];
    memset(tmp, 0, 256);
    size_t bl = c.bl;
    memcpy(tmp, c.buf, bl);
    tmp[bl++] = 0x80;
    if (bl > 112) {
        while (bl < 128) tmp[bl++] = 0;
        sha512_block(c, tmp);
        memset(tmp, 0, 256);
        bl = 0;
    }
    while (bl < 112) tmp[bl++] = 0;
    for (int i = 0; i < 8; i++) tmp[120 + i] = u8(bits >> (56 - i*8));
    sha512_block(c, tmp);
    for (int i = 0; i < 8; i++) {
        for (int j = 0; j < 8; j++) out[i*8+j] = u8(c.h[i] >> (56 - j*8));
    }
}

static void sha512(const u8* p, size_t n, u8 out[64]) {
    Sha512Ctx c; sha512_init(c); sha512_update(c, p, n); sha512_final(c, out);
}

static void hmac_sha512(const u8* key, size_t klen, const u8* msg, size_t mlen, u8 out[64]) {
    u8 k[128], ko[64], ki[128];
    memset(k, 0, 128);
    if (klen > 128) { sha512(key, klen, ko); memcpy(k, ko, 64); }
    else memcpy(k, key, klen);
    for (int i = 0; i < 128; i++) { ki[i] = k[i]^0x36; k[i] ^= 0x5c; }
    Sha512Ctx c;
    sha512_init(c); sha512_update(c, ki, 128); sha512_update(c, msg, mlen);
    u8 inner[64]; sha512_final(c, inner);
    sha512_init(c); sha512_update(c, k, 128); sha512_update(c, inner, 64); sha512_final(c, out);
    secure_wipe(k, 128); secure_wipe(ki, 128); secure_wipe(inner, 64);
}

static void hkdf_sha512(const u8* ikm, size_t ilen, const u8* info, size_t infolen, u8* out, size_t olen) {
    u8 zeros[64];
    memset(zeros, 0, 64);
    u8 prk[64];
    hmac_sha512(zeros, 64, ikm, ilen, prk);
    u8 t[64];
    size_t tlen = 0;
    u32 counter = 1;
    size_t got = 0;
    while (got < olen) {
        std::vector<u8> msg(tlen + infolen + 1);
        if (tlen) memcpy(msg.data(), t, tlen);
        if (infolen) memcpy(msg.data() + tlen, info, infolen);
        msg[tlen + infolen] = u8(counter);
        hmac_sha512(prk, 64, msg.data(), msg.size(), t);
        tlen = 64;
        size_t take = std::min(olen - got, size_t(64));
        memcpy(out + got, t, take);
        got += take;
        counter++;
        secure_wipe(msg.data(), msg.size());
    }
    secure_wipe(prk, 64); secure_wipe(t, 64);
}

struct Sha256Hmac {
    u8 ko[64], ki[64];
    void init(const u8* key, size_t klen) {
        u8 k[64];
        memset(k, 0, 64);
        u8 kh[32];
        if (klen > 64) { sha256(key, klen, kh); memcpy(k, kh, 32); }
        else memcpy(k, key, klen);
        for (int i = 0; i < 64; i++) { ki[i] = k[i]^0x36; ko[i] = k[i]^0x5c; }
        secure_wipe(k, 64); secure_wipe(kh, 32);
    }
    void compute2(const u8* m1, size_t l1, const u8* m2, size_t l2, u8 out[32]) const {
        Sha256Ctx c;
        sha256_init(c);
        sha256_update(c, ki, 64);
        if (l1) sha256_update(c, m1, l1);
        if (l2) sha256_update(c, m2, l2);
        u8 inner[32];
        sha256_final(c, inner);
        sha256_init(c);
        sha256_update(c, ko, 64);
        sha256_update(c, inner, 32);
        sha256_final(c, out);
        secure_wipe(inner, 32);
    }
    void compute(const u8* msg, size_t mlen, u8 out[32]) const {
        compute2(msg, mlen, nullptr, 0, out);
    }
};

static void pbkdf2_sha256(const u8* pw, size_t plen, const u8* salt, size_t slen, u64 iters, u8* out, size_t olen) {
    Sha256Hmac hm;
    hm.init(pw, plen);
    u32 block = 1;
    size_t got = 0;
    u8 ib[4];
    u8 u[32], t[32];
    while (got < olen) {
        ib[0] = u8(block>>24); ib[1] = u8(block>>16); ib[2] = u8(block>>8); ib[3] = u8(block);
        hm.compute2(salt, slen, ib, 4, u);
        memcpy(t, u, 32);
        for (u64 i = 1; i < iters; i++) {
            hm.compute(u, 32, u);
            for (int j = 0; j < 32; j++) t[j] ^= u[j];
        }
        size_t take = std::min(olen - got, size_t(32));
        memcpy(out + got, t, take);
        got += take;
        block++;
    }
    secure_wipe(t, 32); secure_wipe(u, 32);
}

static void salsa20_8(u8 b[64]) {
    u32 x[16];
    for (int i = 0; i < 16; i++) {
        x[i] = u32(b[i*4]) | (u32(b[i*4+1])<<8) | (u32(b[i*4+2])<<16) | (u32(b[i*4+3])<<24);
    }
    #define WA_QR(a,bb,c,d,s1,s2,s3,s4) \
        x[a] ^= ((x[bb]+x[d])<<s1 | (x[bb]+x[d])>>(32-s1)); \
        x[c] ^= ((x[a]+x[bb])<<s2 | (x[a]+x[bb])>>(32-s2)); \
        x[d] ^= ((x[c]+x[a])<<s3 | (x[c]+x[a])>>(32-s3)); \
        x[bb] ^= ((x[d]+x[c])<<s4 | (x[d]+x[c])>>(32-s4));
    for (int i = 0; i < 8; i += 2) {
        WA_QR(4,0,8,12,7,9,13,18)
        WA_QR(9,5,13,1,7,9,13,18)
        WA_QR(14,10,2,6,7,9,13,18)
        WA_QR(3,15,7,11,7,9,13,18)
        WA_QR(1,0,2,3,7,9,13,18)
        WA_QR(6,5,7,4,7,9,13,18)
        WA_QR(11,10,8,9,7,9,13,18)
        WA_QR(12,15,13,14,7,9,13,18)
    }
    #undef WA_QR
    for (int i = 0; i < 16; i++) {
        u32 v = x[i] + (u32(b[i*4]) | (u32(b[i*4+1])<<8) | (u32(b[i*4+2])<<16) | (u32(b[i*4+3])<<24));
        b[i*4] = u8(v); b[i*4+1] = u8(v>>8); b[i*4+2] = u8(v>>16); b[i*4+3] = u8(v>>24);
    }
}

static void blockmix(const u8* in, u8* out, size_t r) {
    u8 x[64];
    memcpy(x, in + (2*r-1)*64, 64);
    for (size_t i = 0; i < 2*r; i += 2) {
        for (int j = 0; j < 64; j++) x[j] ^= in[i*64 + j];
        salsa20_8(x);
        memcpy(out + (i/2)*64, x, 64);
        for (int j = 0; j < 64; j++) x[j] ^= in[(i+1)*64 + j];
        salsa20_8(x);
        memcpy(out + (r + i/2)*64, x, 64);
    }
    secure_wipe(x, 64);
}

static u64 le64(const u8* p) {
    return u64(p[0]) | (u64(p[1])<<8) | (u64(p[2])<<16) | (u64(p[3])<<24) |
           (u64(p[4])<<32) | (u64(p[5])<<40) | (u64(p[6])<<48) | (u64(p[7])<<56);
}

static void romix(u8* block, size_t r, u64 n) {
    size_t blen = 128 * r;
    std::vector<u8> v(n * blen, 0);
    std::vector<u8> tmp(blen, 0);
    for (u64 i = 0; i < n; i++) {
        memcpy(&v[i*blen], block, blen);
        blockmix(block, &tmp[0], r);
        memcpy(block, &tmp[0], blen);
    }
    for (u64 i = 0; i < n; i++) {
        u64 j = le64(&block[(2*r-1)*64]) & (n-1);
        for (size_t k = 0; k < blen; k++) block[k] ^= v[j*blen + k];
        blockmix(block, &tmp[0], r);
        memcpy(block, &tmp[0], blen);
    }
    secure_wipe(v.data(), v.size());
    secure_wipe(tmp.data(), tmp.size());
}

static void scrypt(const u8* pw, size_t plen, const u8* salt, size_t slen, u64 n, u32 r, u32 p, u8* out, size_t olen) {
    std::vector<u8> b(128 * r * p, 0);
    pbkdf2_sha256(pw, plen, salt, slen, 1, b.data(), b.size());
    for (u32 i = 0; i < p; i++) {
        romix(b.data() + i * 128 * r, r, n);
    }
    pbkdf2_sha256(pw, plen, b.data(), b.size(), 1, out, olen);
    secure_wipe(b.data(), b.size());
}

static const u8 AES_SB[256] = {
    0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
    0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
    0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
    0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
    0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
    0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
    0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
    0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
    0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
    0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
    0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
    0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
    0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
    0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
    0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
    0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16
};

static inline u8 gf_xtime(u8 a) { return u8((a<<1) ^ ((a>>7)*0x1b)); }

struct AesTables {
    u32 ft[4][256];
    u8 inv[256];
    AesTables() {
        for (int i = 0; i < 256; i++) {
            inv[AES_SB[i]] = u8(i);
            u8 s = AES_SB[i];
            u8 s2 = gf_xtime(s), s3 = u8(s2^s);
            u32 w0 = (u32(s2)<<24)|(u32(s)<<16)|(u32(s)<<8)|u32(s3);
            ft[0][i] = w0;
            ft[1][i] = (w0>>8)|(w0<<24);
            ft[2][i] = (w0>>16)|(w0<<16);
            ft[3][i] = (w0>>24)|(w0<<8);
        }
    }
};
static const AesTables AT;

struct Aes256 {
    u32 rk[60];
    void expand(const u8* key) {
        static const u32 rcon[7] = {0x01000000,0x02000000,0x04000000,0x08000000,0x10000000,0x20000000,0x40000000};
        for (int i = 0; i < 8; i++) {
            rk[i] = (u32(key[i*4])<<24)|(u32(key[i*4+1])<<16)|(u32(key[i*4+2])<<8)|u32(key[i*4+3]);
        }
        for (int i = 8; i < 60; i++) {
            u32 t = rk[i-1];
            if (i % 8 == 0) {
                t = (t<<8)|(t>>24);
                t = ((u32(AES_SB[(t>>24)&0xff])<<24)|((u32(AES_SB[(t>>16)&0xff])<<16))|((u32(AES_SB[(t>>8)&0xff])<<8))|u32(AES_SB[t&0xff]));
                t ^= rcon[i/8 - 1];
            } else if (i % 8 == 4) {
                t = ((u32(AES_SB[(t>>24)&0xff])<<24)|((u32(AES_SB[(t>>16)&0xff])<<16))|((u32(AES_SB[(t>>8)&0xff])<<8))|u32(AES_SB[t&0xff]));
            }
            rk[i] = rk[i-8] ^ t;
        }
    }
    void enc_block(const u8* in, u8* out) const {
        u32 s0 = rk[0]^((u32(in[0])<<24)|(u32(in[1])<<16)|(u32(in[2])<<8)|u32(in[3]));
        u32 s1 = rk[1]^((u32(in[4])<<24)|(u32(in[5])<<16)|(u32(in[6])<<8)|u32(in[7]));
        u32 s2 = rk[2]^((u32(in[8])<<24)|(u32(in[9])<<16)|(u32(in[10])<<8)|u32(in[11]));
        u32 s3 = rk[3]^((u32(in[12])<<24)|(u32(in[13])<<16)|(u32(in[14])<<8)|u32(in[15]));
        u32 t0,t1,t2,t3;
        #define WA_RND(n) \
            t0 = AT.ft[0][(s0>>24)&0xff]^AT.ft[1][(s1>>16)&0xff]^AT.ft[2][(s2>>8)&0xff]^AT.ft[3][s3&0xff]^rk[n]; \
            t1 = AT.ft[0][(s1>>24)&0xff]^AT.ft[1][(s2>>16)&0xff]^AT.ft[2][(s3>>8)&0xff]^AT.ft[3][s0&0xff]^rk[n+1]; \
            t2 = AT.ft[0][(s2>>24)&0xff]^AT.ft[1][(s3>>16)&0xff]^AT.ft[2][(s0>>8)&0xff]^AT.ft[3][s1&0xff]^rk[n+2]; \
            t3 = AT.ft[0][(s3>>24)&0xff]^AT.ft[1][(s0>>16)&0xff]^AT.ft[2][(s1>>8)&0xff]^AT.ft[3][s2&0xff]^rk[n+3]; \
            s0=t0;s1=t1;s2=t2;s3=t3;
        WA_RND(4) WA_RND(8) WA_RND(12) WA_RND(16) WA_RND(20) WA_RND(24) WA_RND(28)
        WA_RND(32) WA_RND(36) WA_RND(40) WA_RND(44) WA_RND(48) WA_RND(52)
        #undef WA_RND
        u32 o0 = rk[56] ^ ((u32(AES_SB[(s0>>24)&0xff])<<24) | (u32(AES_SB[(s1>>16)&0xff])<<16) | (u32(AES_SB[(s2>>8)&0xff])<<8) | u32(AES_SB[s3&0xff]));
        u32 o1 = rk[57] ^ ((u32(AES_SB[(s1>>24)&0xff])<<24) | (u32(AES_SB[(s2>>16)&0xff])<<16) | (u32(AES_SB[(s3>>8)&0xff])<<8) | u32(AES_SB[s0&0xff]));
        u32 o2 = rk[58] ^ ((u32(AES_SB[(s2>>24)&0xff])<<24) | (u32(AES_SB[(s3>>16)&0xff])<<16) | (u32(AES_SB[(s0>>8)&0xff])<<8) | u32(AES_SB[s1&0xff]));
        u32 o3 = rk[59] ^ ((u32(AES_SB[(s3>>24)&0xff])<<24) | (u32(AES_SB[(s0>>16)&0xff])<<16) | (u32(AES_SB[(s1>>8)&0xff])<<8) | u32(AES_SB[s2&0xff]));
        out[0]=u8(o0>>24);out[1]=u8(o0>>16);out[2]=u8(o0>>8);out[3]=u8(o0);
        out[4]=u8(o1>>24);out[5]=u8(o1>>16);out[6]=u8(o1>>8);out[7]=u8(o1);
        out[8]=u8(o2>>24);out[9]=u8(o2>>16);out[10]=u8(o2>>8);out[11]=u8(o2);
        out[12]=u8(o3>>24);out[13]=u8(o3>>16);out[14]=u8(o3>>8);out[15]=u8(o3);
    }
};

struct Ghash {
    std::vector<u8> pt;
    u8 acc[16];
    Ghash() : pt(size_t(16) * 256 * 16, 0) { memset(acc, 0, 16); }
    u8* cell(int pos, int b) { return pt.data() + (size_t(pos) * 256 + b) * 16; }
    void build(const u8* h) {
        for (int b = 0; b < 256; b++) {
            u8 z[16], v[16];
            memset(z, 0, 16);
            memcpy(v, h, 16);
            for (int i = 0; i < 128; i++) {
                if (i < 8 && (b >> (7 - i)) & 1) {
                    for (int j = 0; j < 16; j++) z[j] ^= v[j];
                }
                bool lsb = (v[15] & 1) != 0;
                for (int j = 15; j > 0; j--) v[j] = u8((v[j]>>1) | (v[j-1]<<7));
                v[0] >>= 1;
                if (lsb) v[0] ^= 0xe1;
            }
            memcpy(cell(0, b), z, 16);
            secure_wipe(z, 16); secure_wipe(v, 16);
        }
        for (int pos = 1; pos < 16; pos++) {
            for (int b = 0; b < 256; b++) {
                u8 v[16];
                memcpy(v, cell(pos - 1, b), 16);
                for (int s = 0; s < 8; s++) {
                    bool lsb = (v[15] & 1) != 0;
                    for (int j = 15; j > 0; j--) v[j] = u8((v[j]>>1) | (v[j-1]<<7));
                    v[0] >>= 1;
                    if (lsb) v[0] ^= 0xe1;
                }
                memcpy(cell(pos, b), v, 16);
                secure_wipe(v, 16);
            }
        }
    }
    void block_mul(const u8* x) {
        u8 z[16];
        memset(z, 0, 16);
        for (int j = 0; j < 16; j++) {
            const u8* t = cell(j, x[j]);
            for (int k = 0; k < 16; k++) z[k] ^= t[k];
        }
        memcpy(acc, z, 16);
        secure_wipe(z, 16);
    }
    void update(const u8* d, size_t n) {
        u8 blk[16];
        size_t off = 0;
        while (off + 16 <= n) {
            for (int i = 0; i < 16; i++) blk[i] = acc[i] ^ d[off+i];
            block_mul(blk);
            off += 16;
        }
        if (off < n) {
            memset(blk, 0, 16);
            memcpy(blk, d + off, n - off);
            for (int i = 0; i < 16; i++) blk[i] = acc[i] ^ blk[i];
            block_mul(blk);
        }
        secure_wipe(blk, 16);
    }
};

struct Gcm {
    Aes256 aes;
    u8 h[16];
    u8 j0[16];
    explicit Gcm(const u8* key) {
        memset(h, 0, 16);
        memset(j0, 0, 16);
        aes.expand(key);
        aes.enc_block(h, h);
    }
};

static bool gcm_decrypt(const Aes256& aes, const u8* iv12, const u8* aad, size_t aadlen,
                        u8* data, size_t datalen, const u8* tag) {
    u8 h[16];
    memset(h, 0, 16);
    aes.enc_block(h, h);
    Ghash gh;
    gh.build(h);
    u8 j0[16];
    memcpy(j0, iv12, 12);
    j0[12] = 0; j0[13] = 0; j0[14] = 0; j0[15] = 1;
    gh.update(aad, aadlen);
    gh.update(data, datalen);
    u8 lb[16];
    u64 abits = u64(aadlen) * 8;
    u64 cbits = u64(datalen) * 8;
    for (int i = 0; i < 8; i++) lb[i] = u8(abits >> (56 - i * 8));
    for (int i = 0; i < 8; i++) lb[8 + i] = u8(cbits >> (56 - i * 8));
    for (int i = 0; i < 16; i++) lb[i] = u8(gh.acc[i] ^ lb[i]);
    gh.block_mul(lb);
    u8 ek[16], tag_calc[16];
    aes.enc_block(j0, ek);
    for (int i = 0; i < 16; i++) tag_calc[i] = u8(gh.acc[i] ^ ek[i]);
    secure_wipe(ek, 16);
    u8 diff = 0;
    for (int i = 0; i < 16; i++) diff |= u8(tag_calc[i] ^ tag[i]);
    secure_wipe(tag_calc, 16);
    if (diff != 0) return false;
    u8 cb[16], ks[16];
    memcpy(cb, j0, 16);
    u32 c = 2;
    cb[12] = u8(c >> 24); cb[13] = u8(c >> 16); cb[14] = u8(c >> 8); cb[15] = u8(c);
    size_t off = 0;
    while (off < datalen) {
        aes.enc_block(cb, ks);
        size_t take = std::min(datalen - off, size_t(16));
        for (size_t i = 0; i < take; i++) data[off + i] ^= ks[i];
        off += take;
        c++;
        cb[12] = u8(c >> 24); cb[13] = u8(c >> 16); cb[14] = u8(c >> 8); cb[15] = u8(c);
    }
    secure_wipe(ks, 16); secure_wipe(cb, 16);
    return true;
}

}

namespace vaf {

static const u8 MAGIC[8] = {0xA7, 0x3C, 0x91, 0xF2, 0x08, 0xDE, 0x55, 0x1B};
static const u8 HDR_AAD[8] = {0x11, 0x9C, 0x4B, 0xE7, 0x02, 0x88, 0xAF, 0x3D};
static const u8 META_INFO[12] = {0x9F, 0x1A, 'V', 'A', 'F', '-', 'M', 'E', 'T', 'A', 0x00, 0x01};
static const u8 FILE_INFO[12] = {0xA3, 0x7E, 'V', 'A', 'F', '-', 'F', 'I', 'L', 'E', 0x00, 0x02};
static const size_t META_BLOCK = 512;
static const size_t CHUNK = 65536;
static const size_t TAG_LEN = 16;

static size_t bucket(size_t n, size_t base) {
    if (n <= base) return base;
    size_t b = base;
    while (b < n) b <<= 1;
    return b;
}

static size_t ct_len(size_t padded) {
    if (padded <= CHUNK) return padded + TAG_LEN;
    return padded + TAG_LEN * (padded / CHUNK);
}

struct VafEntry {
    std::string name;
    std::vector<std::string> sec;
    u64 size = 0;
    u64 off = 0;
    u64 len = 0;
    u8 prefix[4] = {0, 0, 0, 0};
    std::string path() const {
        std::string p;
        for (auto& s : sec) { p += s; p += "/"; }
        p += name;
        return p;
    }
};

struct JVal {
    enum T { NUL, NUM, STR, ARR, OBJ } t = NUL;
    double num = 0;
    std::string str;
    std::vector<JVal> arr;
    std::vector<std::pair<std::string, JVal>> obj;
    const JVal* find(const char* k) const {
        if (t != OBJ) return nullptr;
        for (auto& kv : obj) if (kv.first == k) return &kv.second;
        return nullptr;
    }
};

struct JParser {
    const char* p;
    const char* end;
    bool ok = true;
    JParser(const char* s, size_t n) : p(s), end(s + n) {}
    void ws() { while (p < end && (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r')) p++; }
    JVal parse() {
        ws();
        JVal v = value();
        return v;
    }
    JVal value() {
        ws();
        if (p >= end) { ok = false; return JVal(); }
        char c = *p;
        if (c == '{') return object();
        if (c == '[') return array();
        if (c == '"') { JVal v; v.t = JVal::STR; v.str = string(); return v; }
        if (c == 't' && end - p >= 4) { p += 4; JVal v; v.t = JVal::NUM; v.num = 1; return v; }
        if (c == 'f' && end - p >= 5) { p += 5; return JVal(); }
        if (c == 'n' && end - p >= 4) { p += 4; return JVal(); }
        JVal v;
        v.t = JVal::NUM;
        char* e = nullptr;
        v.num = strtod(p, &e);
        if (e == p) { ok = false; return JVal(); }
        p = e;
        return v;
    }
    JVal object() {
        JVal v;
        v.t = JVal::OBJ;
        p++;
        ws();
        if (p < end && *p == '}') { p++; return v; }
        while (p < end) {
            ws();
            if (*p != '"') { ok = false; return v; }
            std::string k = string();
            ws();
            if (p >= end || *p != ':') { ok = false; return v; }
            p++;
            JVal cv = value();
            v.obj.push_back({k, cv});
            ws();
            if (p < end && *p == ',') { p++; continue; }
            if (p < end && *p == '}') { p++; return v; }
            ok = false;
            return v;
        }
        ok = false;
        return v;
    }
    JVal array() {
        JVal v;
        v.t = JVal::ARR;
        p++;
        ws();
        if (p < end && *p == ']') { p++; return v; }
        while (p < end) {
            JVal cv = value();
            v.arr.push_back(cv);
            ws();
            if (p < end && *p == ',') { p++; continue; }
            if (p < end && *p == ']') { p++; return v; }
            ok = false;
            return v;
        }
        ok = false;
        return v;
    }
    std::string string() {
        std::string s;
        if (*p != '"') { ok = false; return s; }
        p++;
        while (p < end) {
            char c = *p;
            if (c == '"') { p++; return s; }
            if (c == '\\') {
                p++;
                if (p >= end) break;
                char e = *p;
                switch (e) {
                    case '"': s += '"'; break;
                    case '\\': s += '\\'; break;
                    case '/': s += '/'; break;
                    case 'b': s += '\b'; break;
                    case 'f': s += '\f'; break;
                    case 'n': s += '\n'; break;
                    case 'r': s += '\r'; break;
                    case 't': s += '\t'; break;
                    case 'u': {
                        if (end - p >= 5) {
                            unsigned cp = 0;
                            for (int i = 1; i <= 4; i++) {
                                char h = p[i];
                                cp <<= 4;
                                if (h >= '0' && h <= '9') cp |= unsigned(h - '0');
                                else if (h >= 'a' && h <= 'f') cp |= unsigned(h - 'a' + 10);
                                else if (h >= 'A' && h <= 'F') cp |= unsigned(h - 'A' + 10);
                                else { ok = false; }
                            }
                            p += 4;
                            if (cp < 0x80) s += char(cp);
                            else if (cp < 0x800) {
                                s += char(0xC0 | (cp >> 6));
                                s += char(0x80 | (cp & 0x3F));
                            } else {
                                s += char(0xE0 | (cp >> 12));
                                s += char(0x80 | ((cp >> 6) & 0x3F));
                                s += char(0x80 | (cp & 0x3F));
                            }
                        }
                        break;
                    }
                    default: ok = false; break;
                }
                p++;
            } else {
                s += c;
                p++;
            }
        }
        ok = false;
        return s;
    }
};

static void json_escape_append(std::string& out, const std::string& s) {
    for (char c : s) {
        switch (c) {
            case '"': out += "\\\""; break;
            case '\\': out += "\\\\"; break;
            case '\b': out += "\\b"; break;
            case '\f': out += "\\f"; break;
            case '\n': out += "\\n"; break;
            case '\r': out += "\\r"; break;
            case '\t': out += "\\t"; break;
            default:
                if (u8(c) < 0x20) {
                    char b[8];
                    snprintf(b, sizeof(b), "\\u%04x", c);
                    out += b;
                } else out += c;
        }
    }
}

struct VafSource {
    virtual ~VafSource() = default;
    virtual bool read_at(u64 off, u8* dst, size_t n) = 0;
    virtual u64 total() = 0;
};

struct FileSource : VafSource {
    FILE* f = nullptr;
    u64 sz = 0;
    bool open(const char* path) {
        f = fopen(path, "rb");
        if (!f) return false;
        fseek(f, 0, SEEK_END);
        sz = u64(ftell(f));
        fseek(f, 0, SEEK_SET);
        return true;
    }
    ~FileSource() override { if (f) fclose(f); }
    bool read_at(u64 off, u8* dst, size_t n) override {
        if (!f) return false;
        std::lock_guard<std::mutex> lk(m);
        if (fseek(f, long(off), SEEK_SET) != 0) return false;
        return fread(dst, 1, n, f) == n;
    }
    u64 total() override { return sz; }
    std::mutex m;
};

static const u8 ENC_PW[43] = { 0x93,0xe9,0x12,0x9b,0x5a,0xd5,0xea,0x2a,0x74,0x16,0x83,0x28,0x01,0xa9,0x74,0x9a,0x5a,0x42,0x9f,0x90,0xc9,0x06,0x9c,0xcf,0x90,0xc2,0x7b,0xc2,0x23,0x0f,0xbb,0x38,0x24,0xa9,0xcc,0x2c,0x63,0x0f,0x19,0xc4,0x53,0xe2,0xce };
static const u8 PW_TAIL[16] = { 0x93,0x09,0x5f,0x90,0x57,0x05,0xe0,0xb1,0x6b,0x13,0xfc,0xb5,0x68,0x9b,0x48,0xed };
static const u8 PW_HASH[32] = { 0x8c,0x8a,0xc3,0x1d,0x98,0x34,0xc5,0xd7,0xa7,0xf8,0x00,0xa8,0xe0,0xc8,0xc8,0x91,0x3a,0x24,0x14,0x49,0xa0,0x94,0xb0,0xa1,0x02,0xad,0xa7,0x62,0xc1,0x9b,0xcc,0x44 };

static inline u32 wa_rol32(u32 v, int n) { return (v << n) | (v >> (32 - n)); }

static bool derive_password(u8 out[43]) {
    u32 st[8];
    st[0] = wa_rol32(0x5A3C91F2u ^ 0x9E3779B9u, 7) | 1u;
    st[1] = st[0] * 0x41C64E6Du + 0x3039u;
    st[2] = st[1] ^ (st[0] >> 5);
    st[3] = wa_rol32(st[2], 13) | 1u;
    st[4] = st[3] * 0x41C64E6Du + 0x3039u;
    st[5] = st[4] ^ (st[3] >> 11);
    st[6] = wa_rol32(st[5], 23) | 1u;
    st[7] = st[6] * 0x41C64E6Du + 0x3039u;
    u8 mask[43 + 16];
    u32 x = 0x5A3C91F2u ^ (st[7] & 0);
    for (size_t i = 0; i < sizeof(mask); i++) {
        x = x * 0x41C64E6Du + 0x3039u;
        mask[i] = u8((x >> 16) & 0xFF);
    }
    u8 sw = u8((st[1] ^ st[6]) & 7);
    for (int step = 0; step < 12; step++) {
        switch ((step + sw) & 7) {
            case 3: { u32 v = st[2] ^ st[5]; st[2] = wa_rol32(v, 7) | 1u; break; }
            case 6: { u32 v = st[3] + st[4]; st[5] ^= wa_rol32(v, 17); break; }
            case 1: { u32 v = st[0] ^ st[7]; st[4] = wa_rol32(v, 11) | 1u; break; }
            case 4: { u32 v = st[6] ^ st[1]; st[7] = wa_rol32(v, 29); break; }
            case 0: { u32 v = st[5] ^ st[2]; st[1] ^= wa_rol32(v, 3); break; }
            case 7: { u32 v = st[4] + st[0]; st[6] = wa_rol32(v, 19) | 1u; break; }
            case 2: { u32 v = st[7] ^ st[3]; st[0] ^= wa_rol32(v, 15); break; }
            default: { u32 v = st[1] ^ st[6]; st[3] += wa_rol32(v, 9); break; }
        }
        if (((st[0] ^ st[7]) & 0xFFFF) == 0xDEAD) return false;
    }
    for (size_t i = 0; i < 43; i++) {
        out[i] = u8(ENC_PW[i] ^ mask[i] ^ PW_TAIL[i % 16]);
    }
    u8 chk[32];
    crypt::sha256(out, 43, chk);
    bool ok = true;
    for (int i = 0; i < 32; i++) ok = ok && chk[i] == PW_HASH[i];
    secure_wipe(chk, 32);
    if (!ok) secure_wipe(out, 43);
    return ok;
}

struct Archive {
    VafSource* src = nullptr;
    u8 salt[32];
    u8 mk[32];
    u64 blob_start = 0;
    std::vector<VafEntry> entries;
    bool ready = false;
    bool opened = false;

    Archive() { memset(salt, 0, 32); memset(mk, 0, 32); }
    ~Archive() { secure_wipe(mk, 32); }

    bool open(VafSource* s) {
        src = s;
        u64 total = src->total();
        if (total < 64) return false;
        u8 head[56];
        if (!src->read_at(0, head, 56)) return false;
        if (memcmp(head, MAGIC, 8) != 0) return false;
        memcpy(salt, head + 8, 32);
        u64 ml = (u64(head[40]) << 24) | (u64(head[41]) << 16) | (u64(head[42]) << 8) | u64(head[43]);
        if (ml == 0 || ml > 64 * 1024 * 1024 || ml > total - 56) return false;
        u8 mn[12];
        memcpy(mn, head + 44, 12);
        blob_start = 56 + ml;
        std::vector<u8> mct(ml);
        if (!src->read_at(56, mct.data(), ml)) return false;
        if (ml < 20) return false;
        u64 mclen = ml - 16;
        u8 pw[43];
        if (!derive_password(pw)) return false;
        u8 mkbuf[32];
        crypt::scrypt(pw, 43, salt, 32, u64(1) << 17, 8, 1, mkbuf, 32);
        secure_wipe(pw, 43);
        memcpy(mk, mkbuf, 32);
        secure_wipe(mkbuf, 32);
        std::vector<u8> aad(48);
        memcpy(aad.data(), HDR_AAD, 8);
        memcpy(aad.data() + 8, MAGIC, 8);
        memcpy(aad.data() + 16, salt, 32);
        crypt::Aes256 aes;
        u8 fmk[32];
        crypt::hkdf_sha512(mk, 32, META_INFO, 12, fmk, 32);
        aes.expand(fmk);
        secure_wipe(fmk, 32);
        std::vector<u8> mp(mclen);
        memcpy(mp.data(), mct.data(), mclen);
        u8 mtag[16];
        memcpy(mtag, mct.data() + mclen, 16);
        secure_wipe(mct.data(), mct.size());
        if (!crypt::gcm_decrypt(aes, mn, aad.data(), 48, mp.data(), mclen, mtag)) {
            return false;
        }
        if (ml < 4) return false;
        u64 plen = (u64(mp[0]) << 24) | (u64(mp[1]) << 16) | (u64(mp[2]) << 8) | u64(mp[3]);
        if (plen > mclen - 4) return false;
        JParser jp((const char*)mp.data() + 4, plen);
        JVal root = jp.parse();
        if (!jp.ok || root.t != JVal::OBJ) return false;
        const JVal* files = root.find("files");
        if (!files || files->t != JVal::ARR) return false;
        entries.clear();
        for (auto& fv : files->arr) {
            if (fv.t != JVal::OBJ) continue;
            VafEntry e;
            const JVal* n = fv.find("n");
            const JVal* sz = fv.find("s");
            const JVal* off = fv.find("o");
            const JVal* ln = fv.find("l");
            const JVal* pr = fv.find("p");
            const JVal* sec = fv.find("sec");
            if (!n || n->t != JVal::STR) continue;
            if (!sz || !off || !ln) continue;
            e.name = n->str;
            e.size = u64(sz->num);
            e.off = u64(off->num);
            e.len = u64(ln->num);
            if (pr && pr->t == JVal::STR && pr->str.size() == 8) {
                for (int i = 0; i < 4; i++) {
                    char h0 = pr->str[i * 2], h1 = pr->str[i * 2 + 1];
                    auto hv = [](char c) -> int {
                        if (c >= '0' && c <= '9') return c - '0';
                        if (c >= 'a' && c <= 'f') return c - 'a' + 10;
                        if (c >= 'A' && c <= 'F') return c - 'A' + 10;
                        return -1;
                    };
                    int a = hv(h0), b = hv(h1);
                    if (a < 0 || b < 0) { a = 0; b = 0; }
                    e.prefix[i] = u8((a << 4) | b);
                }
            }
            if (sec && sec->t == JVal::ARR) {
                for (auto& sv : sec->arr) if (sv.t == JVal::STR) e.sec.push_back(sv.str);
            }
            if (ct_len(bucket(size_t(e.size), 256)) != size_t(e.len)) continue;
            if (e.off + e.len > total - blob_start) continue;
            entries.push_back(std::move(e));
        }
        ready = !entries.empty();
        opened = true;
        return ready;
    }

    const VafEntry* find(const char* path) const {
        for (auto& e : entries) {
            if (e.path() == path) return &e;
        }
        return nullptr;
    }

    void file_key(const VafEntry& e, u8 out[32]) const {
        std::string info;
        info.reserve(16 + e.name.size() + e.sec.size() * 16 + 40);
        info.append((const char*)FILE_INFO, 12);
        info += "[[";
        for (size_t i = 0; i < e.sec.size(); i++) {
            if (i) info += ",";
            info += "\"";
            json_escape_append(info, e.sec[i]);
            info += "\"";
        }
        info += "],\"";
        json_escape_append(info, e.name);
        info += "\"]";
        info += '\0';
        info.append((const char*)salt, 32);
        crypt::hkdf_sha512(mk, 32, (const u8*)info.data(), info.size(), out, 32);
    }

    bool decrypt_range(const VafEntry& e, u64 start_byte, u64 count, u8* out,
                       const std::function<void(u64)>* progress) const {
        if (start_byte + count > e.size) return false;
        size_t padded = bucket(size_t(e.size), 256);
        size_t chunk_sz;
        size_t n_chunks;
        if (padded <= CHUNK) { n_chunks = 1; chunk_sz = padded; }
        else { n_chunks = padded / CHUNK; chunk_sz = CHUNK; }
        u64 first_chunk = start_byte / chunk_sz;
        u64 last_chunk = (start_byte + count - 1) / chunk_sz;
        u8 key[32];
        file_key(e, key);
        crypt::Aes256 aes;
        aes.expand(key);
        secure_wipe(key, 32);
        u8 aad[52];
        memcpy(aad, HDR_AAD, 8);
        memcpy(aad + 8, salt, 32);
        memcpy(aad + 40, e.prefix, 4);
        std::vector<u8> cbuf(chunk_sz + TAG_LEN);
        u64 done = 0;
        for (u64 ci = first_chunk; ci <= last_chunk; ci++) {
            u64 coff = ci * (chunk_sz + TAG_LEN);
            if (!src->read_at(blob_start + e.off + coff, cbuf.data(), chunk_sz + TAG_LEN)) return false;
            u8 idxb[8];
            for (int i = 0; i < 8; i++) idxb[i] = u8(ci >> (56 - i * 8));
            memcpy(aad + 44, idxb, 8);
            u8 iv[12];
            memcpy(iv, e.prefix, 4);
            memcpy(iv + 4, idxb, 8);
            u8 ctag[16];
            memcpy(ctag, cbuf.data() + chunk_sz, TAG_LEN);
            if (!crypt::gcm_decrypt(aes, iv, aad, 52, cbuf.data(), chunk_sz, ctag)) {
                return false;
            }
            u64 in_chunk_start = (ci == first_chunk) ? start_byte % chunk_sz : 0;
            u64 take = std::min<u64>(count - done, chunk_sz - in_chunk_start);
            memcpy(out + done, cbuf.data() + in_chunk_start, size_t(take));
            done += take;
            if (progress) (*progress)(done);
        }
        return true;
    }

    bool extract(const VafEntry& e, Bytes& out) {
        out.d.resize(size_t(e.size));
        if (e.size == 0) return true;
        return decrypt_range(e, 0, e.size, out.data(), nullptr);
    }

    bool extract_stream(const VafEntry& e, const std::function<bool(const u8*, size_t)>& sink,
                        const std::function<void(u64)>& progress) {
        size_t padded = bucket(size_t(e.size), 256);
        size_t chunk_sz;
        size_t n_chunks;
        if (padded <= CHUNK) { n_chunks = 1; chunk_sz = padded; }
        else { n_chunks = padded / CHUNK; chunk_sz = CHUNK; }
        u8 key[32];
        file_key(e, key);
        crypt::Aes256 aes;
        aes.expand(key);
        secure_wipe(key, 32);
        u8 aad[52];
        memcpy(aad, HDR_AAD, 8);
        memcpy(aad + 8, salt, 32);
        memcpy(aad + 40, e.prefix, 4);
        std::vector<u8> cbuf(chunk_sz + TAG_LEN);
        std::vector<u8> pbuf(chunk_sz);
        u64 remaining = e.size;
        for (size_t ci = 0; ci < n_chunks; ci++) {
            if (!src->read_at(blob_start + e.off + ci * (chunk_sz + TAG_LEN), cbuf.data(), chunk_sz + TAG_LEN)) return false;
            u8 idxb[8];
            for (int i = 0; i < 8; i++) idxb[i] = u8(ci >> (56 - i * 8));
            memcpy(aad + 44, idxb, 8);
            u8 iv[12];
            memcpy(iv, e.prefix, 4);
            memcpy(iv + 4, idxb, 8);
            u8 ctag[16];
            memcpy(ctag, cbuf.data() + chunk_sz, TAG_LEN);
            if (!crypt::gcm_decrypt(aes, iv, aad, 52, cbuf.data(), chunk_sz, ctag)) {
                return false;
            }
            u64 take = std::min<u64>(remaining, chunk_sz);
            if (take > 0 && !sink(cbuf.data(), size_t(take))) return false;
            remaining -= take;
            progress(e.size - remaining);
            if (remaining == 0) break;
        }
        return true;
    }
};

}

}

namespace wa {

namespace security {

enum Event {
    EVENT_NONE = 0,
    EVENT_ROOT = 1,
    EVENT_TAMPER = 2,
    EVENT_WINDOWS_EMULATOR = 3
};

enum Stage {
    STAGE_ROOT = 0,
    STAGE_FRIDA = 1,
    STAGE_MAGISK = 2,
    STAGE_WINDOWS_EMULATOR = 3
};

static std::atomic<int> g_event{EVENT_NONE};
static std::atomic<int> g_stage{STAGE_ROOT};
static std::atomic<bool> g_running{false};

static long long now_ms() {
    return std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::steady_clock::now().time_since_epoch()).count();
}

static std::string lower_copy(const std::string& s) {
    std::string out = s;
    for (char& c : out) c = char(std::tolower(static_cast<unsigned char>(c)));
    return out;
}

static bool contains_ci(const std::string& s, const char* needle) {
    return lower_copy(s).find(lower_copy(needle)) != std::string::npos;
}

static bool contains_word_ci(const std::string& s, const char* word) {
    std::string low = lower_copy(s);
    std::string w = lower_copy(word);
    if (w.empty()) return false;
    size_t p = 0;
    while ((p = low.find(w, p)) != std::string::npos) {
        bool lb = (p == 0) || !std::isalnum((unsigned char)low[p - 1]);
        size_t e = p + w.size();
        bool rb = (e >= low.size()) || !std::isalnum((unsigned char)low[e]);
        if (lb && rb) return true;
        p = e;
    }
    return false;
}

static bool path_exists(const char* path) {
    struct stat st{};
    return stat(path, &st) == 0;
}

static bool file_contains_ci(const char* path, const char* needle) {
    FILE* f = fopen(path, "rb");
    if (!f) return false;
    char buf[4096];
    size_t n = 0;
    std::string carry;
    const std::string nl = lower_copy(needle);
    bool found = false;
    while ((n = fread(buf, 1, sizeof(buf), f)) > 0) {
        std::string chunk = carry;
        chunk.append(buf, n);
        if (lower_copy(chunk).find(nl) != std::string::npos) {
            found = true;
            break;
        }
        if (nl.size() > 1 && chunk.size() >= nl.size() - 1)
            carry = chunk.substr(chunk.size() - (nl.size() - 1));
        else
            carry.clear();
    }
    fclose(f);
    return found;
}

static bool regular_or_symlink_exists(const char* path) {
    struct stat st{};
    return lstat(path, &st) == 0;
}

static bool executable_exists(const char* path) {
    return access(path, X_OK) == 0;
}

static bool mapped_library_contains(const char* marker) {
    FILE* f = fopen("/proc/self/maps", "rb");
    if (!f) return false;
    char line[2048];
    const std::string needle = lower_copy(marker);
    bool found = false;
    while (fgets(line, sizeof(line), f)) {
        std::string s = lower_copy(std::string(line));
        size_t sp = s.find_last_of(' ');
        if (sp == std::string::npos) continue;
        std::string path = s.substr(sp + 1);
        while (!path.empty() && (path.back() == '\n' || path.back() == '\r' || path.back() == ' ')) path.pop_back();
        size_t slash = path.find_last_of('/');
        std::string fname = slash == std::string::npos ? path : path.substr(slash + 1);
        if (fname.find(needle) != std::string::npos) {
            found = true;
            break;
        }
    }
    fclose(f);
    return found;
}

static bool task_name_contains(const char* marker) {
#ifdef __ANDROID__
    DIR* dir = opendir("/proc/self/task");
    if (!dir) return false;
    struct dirent* ent = nullptr;
    bool found = false;
    while ((ent = readdir(dir)) != nullptr) {
        if (ent->d_name[0] == '.') continue;
        std::string path = std::string("/proc/self/task/") + ent->d_name + "/comm";
        FILE* f = fopen(path.c_str(), "rb");
        if (!f) continue;
        char buf[256]{};
        if (fgets(buf, sizeof(buf), f)) {
            if (contains_ci(std::string(buf), marker)) {
                found = true;
                fclose(f);
                break;
            }
        }
        fclose(f);
    }
    closedir(dir);
    return found;
#else
    (void)marker;
    return false;
#endif
}

#ifdef __ANDROID__
static std::string prop(const char* name) {
    char buf[PROP_VALUE_MAX]{};
    __system_property_get(name, buf);
    return std::string(buf);
}
#else
static std::string prop(const char*) {
    return "";
}
#endif

static bool root_uid_signal() {
    return getuid() == 0 || geteuid() == 0;
}

static bool root_capability_signal() {
#ifdef __ANDROID__
    FILE* f = fopen("/proc/self/status", "rb");
    if (!f) return false;
    char line[256];
    bool found = false;
    while (fgets(line, sizeof(line), f)) {
        if (strncmp(line, "CapEff:", 7) == 0) {
            const char* p = line + 7;
            while (*p == ' ' || *p == '\t') ++p;
            unsigned long long caps = strtoull(p, nullptr, 16);
            const unsigned long long privileged =
                (1ULL << 6) | (1ULL << 7) | (1ULL << 16) |
                (1ULL << 17) | (1ULL << 19) | (1ULL << 21);
            found = (caps & privileged) != 0;
            break;
        }
    }
    fclose(f);
    return found;
#else
    return false;
#endif
}

static bool root_su_signal() {
    static const char* paths[] = {
        "/system/xbin/su", "/system/bin/su", "/sbin/su", "/su/bin/su",
        "/data/local/tmp/su", "/data/local/su", "/data/local/bin/su",
        "/data/local/xbin/su", "/vendor/bin/su", "/vendor/xbin/su",
        "/magisk/.core/bin/su"
    };
    for (const char* p : paths) {
        if (regular_or_symlink_exists(p) && executable_exists(p)) return true;
    }
    return false;
}

static bool root_busybox_signal() {
    static const char* paths[] = {"/system/xbin/busybox", "/system/bin/busybox"};
    for (const char* p : paths) {
        if (regular_or_symlink_exists(p) && executable_exists(p)) return true;
    }
    return false;
}

static bool root_legacy_package_signal() {
    static const char* paths[] = {
        "/system/app/Superuser.apk", "/system/app/SuperSU", "/system/app/SuperSU.apk"
    };
    int hits = 0;
    for (const char* p : paths) if (path_exists(p)) ++hits;
    return hits >= 1 && (root_uid_signal() || root_capability_signal() || root_su_signal());
}

static bool kernelsu_signal() {
#ifdef __ANDROID__
    const bool artifact =
        path_exists("/data/adb/ksu") ||
        path_exists("/data/adb/ksud") ||
        path_exists("/data/adb/ksu/modules.img") ||
        path_exists("/sys/module/ksu") ||
        path_exists("/sys/module/kernelsu");
    if (!artifact) return false;
    if (root_uid_signal() || root_capability_signal()) return true;
    if (mapped_library_contains("libksu") || mapped_library_contains("ksud")) return true;
    if (file_contains_ci("/proc/modules", "kernelsu") ||
        file_contains_ci("/proc/self/mountinfo", "ksu")) return true;
    FILE* f = fopen("/sys/fs/selinux/enforce", "rb");
    if (f) {
        char v = '1';
        const bool permissive = fread(&v, 1, 1, f) == 1 && v == '0';
        fclose(f);
        if (permissive) return true;
    }
#endif
    return false;
}

static bool root_artifact_signal() {
#ifdef __ANDROID__
    static const char* paths[] = {
        "/data/adb/magisk", "/data/adb/ap", "/data/adb/zygisk",
        "/data/adb/lspinstallersrv", "/data/adb/modules/zygisksu",
        "/data/adb/modules/riru_core", "/sbin/.magisk",
        "/data/adb/modules_update", "/data/adb/post-fs-data.d",
        "/data/adb/service.d"
    };
    int hits = 0;
    for (const char* p : paths) if (path_exists(p)) ++hits;
    const bool privileged = root_uid_signal() || root_capability_signal() || root_su_signal();
    if (!privileged) return false;
    if (hits >= 1) return true;
    if (file_contains_ci("/proc/self/mountinfo", "magisk") ||
        file_contains_ci("/proc/self/mounts", "magisk")) return true;
#endif
    return false;
}

static bool root_detected() {
    return root_uid_signal() ||
           root_capability_signal() ||
           root_su_signal() ||
           root_busybox_signal() ||
           root_legacy_package_signal() ||
           kernelsu_signal() ||
           root_artifact_signal();
}

static bool frida_interfering() {
    static const char* mapped[] = {
        "frida-agent", "frida-gadget", "libfrida-gum",
        "frida-gum", "gum-js-loop"
    };
    for (const char* m : mapped) if (mapped_library_contains(m)) return true;
    return task_name_contains("gum-js-loop") || task_name_contains("frida");
}

static bool magisk_interfering() {
#ifdef __ANDROID__
    if (!root_uid_signal() && !root_capability_signal()) {
        FILE* f = fopen("/proc/self/status", "rb");
        bool has_root_cap = false;
        if (f) {
            char line[256];
            while (fgets(line, sizeof(line), f)) {
                if (strncmp(line, "CapEff:", 7) == 0) {
                    const char* p = line + 7;
                    while (*p == ' ' || *p == '\t') ++p;
                    unsigned long long caps = strtoull(p, nullptr, 16);
                    if (caps & ((1ULL << 6) | (1ULL << 7) | (1ULL << 21))) has_root_cap = true;
                    break;
                }
            }
            fclose(f);
        }
        if (!has_root_cap) {
            const bool daemon =
                mapped_library_contains("magiskd") ||
                mapped_library_contains("libzygisk") ||
                mapped_library_contains("riru-core") ||
                mapped_library_contains("lsposed") ||
                mapped_library_contains("liblspd");
            return daemon;
        }
    }
    static const char* mapped[] = {
        "libzygisk", "magiskd", "riru-core", "liblspd",
        "lsposed", "libksu", "ksud"
    };
    for (const char* m : mapped) if (mapped_library_contains(m)) return true;
#endif
    return false;
}

static bool windows_emulator_detected() {
#ifdef __ANDROID__
    static const char* strong[] = {
        "bluestacks", "bluestacksx", "noxplayer", "memu", "ldplayer",
        "gameloop", "mumuplayer", "droid4x", "windroy", "koplayer",
        "windows subsystem for android"
    };
    for (const char* m : strong) {
        if (contains_ci(prop("ro.product.brand"), m)) return true;
        if (contains_ci(prop("ro.product.manufacturer"), m)) return true;
        if (contains_ci(prop("ro.product.model"), m)) return true;
        if (contains_ci(prop("ro.hardware"), m)) return true;
        if (contains_ci(prop("ro.build.fingerprint"), m)) return true;
        if (contains_ci(prop("ro.boot.hardware"), m)) return true;
    }
    const std::string manufacturer = lower_copy(prop("ro.product.manufacturer"));
    const std::string model = lower_copy(prop("ro.product.model"));
    const std::string hardware = lower_copy(prop("ro.hardware"));
    const std::string fingerprint = lower_copy(prop("ro.build.fingerprint"));
    if (manufacturer.find("microvirt") != std::string::npos) return true;
    if (manufacturer.find("bluestacks") != std::string::npos) return true;
    if (model.find("bluestacks") != std::string::npos) return true;
    if (model.find("nox") != std::string::npos) return true;
    if (model.find("ldplayer") != std::string::npos) return true;
    if (model.find("mumu") != std::string::npos) return true;
    if (hardware.find("vbox") != std::string::npos) return true;
    if (hardware.find("nox") != std::string::npos) return true;
    if (hardware.find("mumu") != std::string::npos) return true;
    if (fingerprint.find("bluestacks") != std::string::npos) return true;
    if (fingerprint.find("nox") != std::string::npos) return true;
    if (fingerprint.find("ldplayer") != std::string::npos) return true;
    if (fingerprint.find("mumu") != std::string::npos) return true;
    if (file_contains_ci("/proc/version", "windows subsystem for android")) return true;
#endif
    return false;
}

static const u8 WA_NOTE_X[] = {
    0xF5,0xDF,0xDE,0xDF,0x8A,0xDC,0xDF,0xD8,0x8A,0xCB,0xC3,0x8A,0xDB,0xDA,0xDA,
    0xC3,0xDA,0xDB,0xDB,0xDE,0xDB,0xDA,0x8A,0x99,0xDA,0xDB,0xCB,0xDF,0x8A,
    0x99,0xDE,0xCB,0xCF,0xDF,0xDF,0x8A,0x8A,0x9F,0xD8,0xDF,0xC5,0x8A,0xDB,
    0xDA,0xCF,0x8A,0xDB,0xDA,0xC3,0x8A,0xDF,0xDB,0xC3,0xDF,0xD8,0x8A,
    0xCB,0xC3,0x8A,0xDB,0xDE,0xDE,0xC3,0xDE,0xCF,0xDB,0xDA,0xCF,0x9B,
    0x8A,0x9F,0xC3,0xC3,0xDE,0x8A,0xDD,0xD8,0xDF,0xCB,0xC5,0xDA,0xCF,
    0x8A,0xC3,0xDE,0x8A,0xC3,0xDA,0xCF,0xDF,0xDA,0xCF,0xC3,0xDB,0xDA,
    0xDB,0xC6,0xC6,0xD4,0x8A,0xDD,0xD8,0xDF,0xCF,0xDF,0xDA,0xCF,0xDF,
    0xC5,0x8A,0xDB,0xC5,0xDB,0xC3,0xDA,0xDE,0xCF,0x8A,0xD8,0xDF,0xC1,
    0xDF,0xD8,0xDE,0xDF,0x8A,0xDF,0xDA,0xC5,0xC3,0xDA,0xDF,0xDF,0xD8,
    0xC3,0xDA,0xC5,0x8A,0xDB,0xDA,0xCF,0x8A,0xC7,0xDB,0xCF,0xC3,0xDC,
    0xC3,0xDD,0xDB,0xDB,0xCF,0xC3,0xDB,0xDA,0x9B,0x8A,0xC3,0xDC,0x8A,
    0xDB,0x8A,0xDF,0xDF,0xDF,0x8A,0xDF,0xDF,0xDF,0x8A,0xD8,0xDF,0xC1,
    0xDF,0xD8,0xDE,0xDF,0x8A,0xDF,0xDA,0xC5,0xC3,0xDA,0xDF,0xDF,0xD8,
    0x8A,0xDB,0xD8,0x8A,0xDC,0xDB,0xC5,0xC3,0xDD,0xD4,0x8A,0xCF,0xC3,
    0xC3,0xDF,0x8A,0xDD,0xD8,0xDB,0xC5,0xDE,0xDD,0xCF,0x9B,0x8A,
    0xAB,0x9D,0x9C,0xA8,0xA3,0x9D,0x8A,0xCF,0xC3,0xDF,0x8A,0xD8,
    0xDF,0xC1,0xDF,0xD8,0xDE,0xDF,0x9C,0x9F,0xDF,0x8A,0xA2,0x9F,
    0xDF,0xDF,0xDF,0xDF,0xDF,0xDF,0xDF,0xDF,0xDF,0xDF,0xDF,0xDF
};

static void wa_embed_touch() {
    volatile char b[sizeof(WA_NOTE_X)];
    volatile u32 h = 0x811C9DC5u;
    for (size_t i = 0; i < sizeof(WA_NOTE_X); i++) {
        b[i] = char(WA_NOTE_X[i] ^ 0xAA);
        h = (h ^ u8(b[i])) * 0x01000193u;
    }
    (void)h;
    secure_wipe((void*)b, sizeof(b));
}

static void set_block(int event) {
    int expected = EVENT_NONE;
    g_event.compare_exchange_strong(expected, event);
}

static void set_fatal() {
    int expected = EVENT_NONE;
    g_event.compare_exchange_strong(expected, EVENT_TAMPER);
}

static bool advance_stage() {
    const int stage = g_stage.load();
    if (stage == STAGE_ROOT) {
        g_stage.store(STAGE_FRIDA);
        return true;
    }
    if (stage == STAGE_FRIDA) {
        g_stage.store(STAGE_MAGISK);
        return true;
    }
    if (stage == STAGE_MAGISK) {
        g_stage.store(STAGE_WINDOWS_EMULATOR);
        return true;
    }
    if (stage == STAGE_WINDOWS_EMULATOR) {
        if (windows_emulator_detected()) { set_block(EVENT_WINDOWS_EMULATOR); return false; }
        g_stage.store(STAGE_ROOT);
        return true;
    }
    g_stage.store(STAGE_ROOT);
    return true;
}

static void loop() {
    while (g_running.load()) {
        const int ev = g_event.load();
        if (ev != EVENT_NONE) {
            std::this_thread::sleep_for(std::chrono::milliseconds(150));
            continue;
        }
        advance_stage();
        std::this_thread::sleep_for(std::chrono::milliseconds(120));
    }
}

static void start() {
    if (g_running.exchange(true)) return;
    g_event.store(EVENT_NONE);
    g_stage.store(STAGE_ROOT);
    wa_embed_touch();
    std::thread(loop).detach();
}

static int event() { return g_event.load(); }
static void shutdown() { g_running.store(false); }

}

}

namespace wa {

namespace img {

struct Image {
    u32 w = 0, h = 0;
    std::vector<u8> px;
};

static u32 read_be32(const u8* p) {
    return (u32(p[0]) << 24) | (u32(p[1]) << 16) | (u32(p[2]) << 8) | u32(p[3]);
}

static int paeth(int a, int b, int c) {
    int p = a + b - c;
    int pa = p > a ? p - a : a - p;
    int pb = p > b ? p - b : b - p;
    int pc = p > c ? p - c : c - p;
    if (pa <= pb && pa <= pc) return a;
    if (pb <= pc) return b;
    return c;
}

static bool decode_png(const u8* d, size_t n, Image& out) {
    static const u8 sig[8] = {0x89, 'P', 'N', 'G', 0x0D, 0x0A, 0x1A, 0x0A};
    if (n < 57 || memcmp(d, sig, 8) != 0) return false;
    size_t off = 8;
    u32 w = 0, h = 0;
    int depth = 0, color = -1, interlace = 0;
    std::vector<u8> idat;
    std::vector<u8> plte;
    std::vector<u8> trns;
    bool ihdr_ok = false;
    while (off + 8 <= n) {
        u32 len = read_be32(d + off);
        if (off + 12 + len > n) return false;
        const u8* type = d + off + 4;
        const u8* data = d + off + 8;
        if (memcmp(type, "IHDR", 4) == 0 && len >= 13) {
            w = read_be32(data);
            h = read_be32(data + 4);
            depth = data[8];
            color = data[9];
            interlace = data[12];
            ihdr_ok = true;
        } else if (memcmp(type, "PLTE", 4) == 0) {
            plte.assign(data, data + len);
        } else if (memcmp(type, "tRNS", 4) == 0) {
            trns.assign(data, data + len);
        } else if (memcmp(type, "IDAT", 4) == 0) {
            idat.insert(idat.end(), data, data + len);
        } else if (memcmp(type, "IEND", 4) == 0) {
            break;
        }
        off += 12 + len;
    }
    if (!ihdr_ok || idat.empty() || w == 0 || h == 0 || w > 8192 || h > 8192) return false;
    if (depth != 8 || interlace != 0) return false;
    int channels;
    switch (color) {
        case 0: channels = 1; break;
        case 2: channels = 3; break;
        case 3: channels = 1; break;
        case 4: channels = 2; break;
        case 6: channels = 4; break;
        default: return false;
    }
    u64 raw_size = u64(h) * (u64(w) * channels + 1);
    if (raw_size > 512u * 1024 * 1024) return false;
    std::vector<u8> raw((size_t(raw_size)));
    z_stream zs;
    memset(&zs, 0, sizeof(zs));
    if (inflateInit(&zs) != Z_OK) return false;
    zs.next_in = const_cast<u8*>(idat.data());
    zs.avail_in = u32(idat.size());
    zs.next_out = raw.data();
    zs.avail_out = u32(raw.size());
    int zr = inflate(&zs, Z_FINISH);
    inflateEnd(&zs);
    if (zr != Z_STREAM_END) return false;
    size_t stride = size_t(w) * channels;
    std::vector<u8> unr(stride * h);
    const u8* prev = nullptr;
    for (u32 y = 0; y < h; y++) {
        const u8* src = raw.data() + size_t(y) * (stride + 1);
        int ft = src[0];
        u8* dst = unr.data() + size_t(y) * stride;
        for (size_t x = 0; x < stride; x++) {
            int a = (x >= size_t(channels)) ? dst[x - channels] : 0;
            int b = prev ? prev[x] : 0;
            int c = (prev && x >= size_t(channels)) ? prev[x - channels] : 0;
            int v = src[1 + x];
            switch (ft) {
                case 0: dst[x] = v; break;
                case 1: dst[x] = u8(v + a); break;
                case 2: dst[x] = u8(v + b); break;
                case 3: dst[x] = u8(v + ((a + b) >> 1)); break;
                case 4: dst[x] = u8(v + paeth(a, b, c)); break;
                default: return false;
            }
        }
        prev = dst;
    }
    out.w = w;
    out.h = h;
    out.px.resize(size_t(w) * h * 4);
    for (u32 y = 0; y < h; y++) {
        const u8* row = unr.data() + size_t(y) * stride;
        u8* o = out.px.data() + size_t(y) * w * 4;
        for (u32 x = 0; x < w; x++) {
            const u8* s = row + size_t(x) * channels;
            u8* q = o + size_t(x) * 4;
            switch (color) {
                case 0: {
                    u8 g = s[0];
                    u8 a = 255;
                    if (trns.size() >= 2) {
                        u16 tv = u16((trns[0] << 8) | trns[1]);
                        if (tv == u16(g)) a = 0;
                    }
                    q[0] = g; q[1] = g; q[2] = g; q[3] = a;
                    break;
                }
                case 2: q[0] = s[0]; q[1] = s[1]; q[2] = s[2]; q[3] = 255; break;
                case 3: {
                    u32 idx = s[0];
                    if (size_t(idx) * 3 + 2 < plte.size()) {
                        q[0] = plte[idx * 3];
                        q[1] = plte[idx * 3 + 1];
                        q[2] = plte[idx * 3 + 2];
                    } else {
                        q[0] = q[1] = q[2] = 0;
                    }
                    q[3] = (idx < trns.size()) ? trns[idx] : 255;
                    break;
                }
                case 4: q[0] = q[1] = q[2] = s[0]; q[3] = s[1]; break;
                case 6: q[0] = s[0]; q[1] = s[1]; q[2] = s[2]; q[3] = s[3]; break;
            }
        }
    }
    return true;
}

} 


namespace fontx {

struct Edge {
    float x0, y0, x1, y1;
};

struct GlyphBitmap {
    int w, h;
    int bearing_x, bearing_y;
    float advance;
    int atlas_x, atlas_y, page;
    std::vector<u8> cov;
    bool valid = false;
};

struct Font {
    std::vector<u8> data;
    u16 units_per_em = 1000;
    i16 ascender = 800, descender = -200;
    u16 num_glyphs = 0;
    u16 num_hmetrics = 0;
    bool long_loca = false;
    u32 head_off = 0, hhea_off = 0, maxp_off = 0, cmap_off = 0, loca_off = 0, loca_len = 0, glyf_off = 0, hmtx_off = 0;
    u32 cmap4_off = 0, cmap12_off = 0, cmap0_off = 0;
    bool loaded = false;

    static u16 rd16(const u8* p) { return u16(p[0] << 8 | p[1]); }
    static u32 rd32(const u8* p) { return (u32(p[0]) << 24) | (u32(p[1]) << 16) | (u32(p[2]) << 8) | u32(p[3]); }
    static i16 rdi16(const u8* p) { return i16(rd16(p)); }

    bool init(const u8* d, size_t n) {
        data.assign(d, d + n);
        if (data.size() < 12) return false;
        u32 sfnt = rd32(data.data());
        if (sfnt != 0x00010000 && sfnt != 0x4F54544F) return false;
        u16 numtables = rd16(data.data() + 4);
        if (size_t(numtables) * 16 + 12 > data.size()) return false;
        for (u16 i = 0; i < numtables; i++) {
            const u8* rec = data.data() + 12 + size_t(i) * 16;
            char tag[5] = {char(rec[0]), char(rec[1]), char(rec[2]), char(rec[3]), 0};
            u32 off = rd32(rec + 8);
            u32 len = rd32(rec + 12);
            if (strcmp(tag, "head") == 0) { head_off = off; }
            else if (strcmp(tag, "hhea") == 0) { hhea_off = off; }
            else if (strcmp(tag, "maxp") == 0) { maxp_off = off; }
            else if (strcmp(tag, "cmap") == 0) { cmap_off = off; }
            else if (strcmp(tag, "loca") == 0) { loca_off = off; loca_len = len; }
            else if (strcmp(tag, "glyf") == 0) { glyf_off = off; }
            else if (strcmp(tag, "hmtx") == 0) { hmtx_off = off; }
        }
        if (!head_off || !hhea_off || !maxp_off || !cmap_off || !loca_off || !glyf_off || !hmtx_off) return false;
        if (head_off + 54 > data.size()) return false;
        units_per_em = rd16(data.data() + head_off + 18);
        long_loca = rdi16(data.data() + head_off + 50) == 1;
        if (hhea_off + 36 > data.size()) return false;
        ascender = rdi16(data.data() + hhea_off + 4);
        descender = rdi16(data.data() + hhea_off + 6);
        num_hmetrics = rd16(data.data() + hhea_off + 34);
        if (maxp_off + 6 > data.size()) return false;
        num_glyphs = rd16(data.data() + maxp_off + 4);
        if (!parse_cmap()) return false;
        loaded = true;
        return true;
    }

    bool parse_cmap() {
        if (cmap_off + 4 > data.size()) return false;
        u16 n = rd16(data.data() + cmap_off + 2);
        for (u16 i = 0; i < n; i++) {
            const u8* rec = data.data() + cmap_off + 4 + size_t(i) * 8;
            u16 platform = rd16(rec);
            u16 encoding = rd16(rec + 2);
            u32 off = rd32(rec + 4);
            if (platform == 3 && (encoding == 1 || encoding == 10)) {
                if (off + 2 <= data.size() - cmap_off) {
                    u16 fmt = rd16(data.data() + cmap_off + off);
                    if (fmt == 4) cmap4_off = cmap_off + off;
                    if (fmt == 12) cmap12_off = cmap_off + off;
                }
            } else if (platform == 0) {
                if (off + 2 <= data.size() - cmap_off) {
                    u16 fmt = rd16(data.data() + cmap_off + off);
                    if (fmt == 4) cmap4_off = cmap_off + off;
                    if (fmt == 12) cmap12_off = cmap_off + off;
                }
            }
        }
        return cmap4_off || cmap12_off;
    }

    u16 map_codepoint(u32 cp) const {
        if (cmap12_off && cmap12_off + 16 <= data.size()) {
            u32 ngroups = rd32(data.data() + cmap12_off + 12);
            const u8* g = data.data() + cmap12_off + 16;
            size_t lo = 0, hi = ngroups;
            while (lo < hi) {
                size_t mid = (lo + hi) / 2;
                const u8* e = g + mid * 12;
                u32 s = rd32(e), en = rd32(e + 4);
                if (cp < s) hi = mid;
                else if (cp > en) lo = mid + 1;
                else return u16(rd32(e + 8) + (cp - s));
            }
        }
        if (cmap4_off && cmap4_off + 14 <= data.size()) {
            u16 segx2 = rd16(data.data() + cmap4_off + 6);
            u16 segcount = segx2 / 2;
            const u8* base = data.data() + cmap4_off + 14;
            const u8* endc = base;
            const u8* startc = base + segx2 + 2;
            const u8* idelta = startc + segx2;
            const u8* idrange = idelta + segx2;
            for (u16 i = 0; i < segcount; i++) {
                u32 en = rd16(endc + i * 2);
                if (cp > en) continue;
                u32 st = rd16(startc + i * 2);
                if (cp < st) return 0;
                i32 delta = rdi16(idelta + i * 2);
                u32 ro = rd16(idrange + i * 2);
                if (ro == 0) return u16(cp + delta);
                const u8* ro_addr = idrange + size_t(i) * 2;
                const u8* gid_addr = ro_addr + ro + size_t(cp - st) * 2;
                if (gid_addr + 1 >= data.data() + data.size()) return 0;
                u16 gid = rd16(gid_addr);
                if (gid == 0) return 0;
                return u16(gid + delta);
            }
        }
        return 0;
    }

    u32 glyph_offset(u16 gid, u32* next_len) const {
        if (gid >= num_glyphs) { if (next_len) *next_len = 0; return 0; }
        u32 off, len;
        if (long_loca) {
            off = rd32(data.data() + loca_off + size_t(gid) * 4);
            len = rd32(data.data() + loca_off + size_t(gid) * 4 + 4) - off;
        } else {
            off = u32(rd16(data.data() + loca_off + size_t(gid) * 2)) * 2;
            len = u32(rd16(data.data() + loca_off + size_t(gid) * 2 + 2)) * 2 - off;
        }
        if (next_len) *next_len = len;
        return glyf_off + off;
    }

    float advance_of(u16 gid) const {
        if (!num_hmetrics) return float(units_per_em) / 2.f;
        u16 idx = gid < num_hmetrics ? gid : u16(num_hmetrics - 1);
        if (hmtx_off + size_t(idx) * 4 + 2 > data.size()) return 0.f;
        return float(rd16(data.data() + hmtx_off + size_t(idx) * 4));
    }
};

struct Raster {
    Font* font = nullptr;
    Font* fallback = nullptr;
    float scale = 1.f;
    std::unordered_map<u64, GlyphBitmap> cache;

    void set_size(float px) {
        scale = px / float(font ? font->units_per_em : 1000);
    }

    u64 key(u32 cp, float px) const {
        return (u64(cp) << 20) | (u64(px * 8.f) & 0xFFFFF);
    }

    void push_component(u16 idx, float dx, float dy, float a, float b, float c, float d,
                        float ox, float oy, std::vector<Edge>& out, int depth) {
        u32 slen = 0;
        u32 soff = font->glyph_offset(idx, &slen);
        if (slen == 0) return;
        i16 snc = font->rdi16(font->data.data() + soff);
        if (snc >= 0) {
            size_t base = out.size();
            append_simple(soff, snc, 0, 0, out, true);
            for (size_t i = base; i < out.size(); i++) {
                float x0 = out[i].x0, y0 = out[i].y0, x1 = out[i].x1, y1 = out[i].y1;
                float nx0 = a * x0 + c * y0 + dx;
                float ny0 = b * x0 + d * y0 + dy;
                float nx1 = a * x1 + c * y1 + dx;
                float ny1 = b * x1 + d * y1 + dy;
                out[i].x0 = nx0 * scale + ox;
                out[i].y0 = -ny0 * scale + oy;
                out[i].x1 = nx1 * scale + ox;
                out[i].y1 = -ny1 * scale + oy;
            }
        } else if (depth < 4) {
            u32 sco = soff + 10;
            while (sco + 4 <= soff + slen) {
                u16 flags = font->rd16(font->data.data() + sco);
                u16 sidx = font->rd16(font->data.data() + sco + 2);
                sco += 4;
                i32 sdx = 0, sdy = 0;
                if (flags & 1) {
                    sdx = font->rdi16(font->data.data() + sco);
                    sdy = font->rdi16(font->data.data() + sco + 2);
                    sco += 4;
                } else {
                    sdx = i8(font->data[sco]);
                    sdy = i8(font->data[sco + 1]);
                    sco += 2;
                }
                float sa = 1, sb = 0, sc = 0, sd = 1;
                if (flags & 8) { sa = float(i16(font->rd16(font->data.data() + sco))) / 16384.f; sco += 2; }
                else if (flags & 0x40) {
                    sa = float(i16(font->rd16(font->data.data() + sco))) / 16384.f;
                    sd = float(i16(font->rd16(font->data.data() + sco + 2))) / 16384.f;
                    sco += 4;
                } else if (flags & 0x80) {
                    sa = float(i16(font->rd16(font->data.data() + sco))) / 16384.f;
                    sb = float(i16(font->rd16(font->data.data() + sco + 2))) / 16384.f;
                    sc = float(i16(font->rd16(font->data.data() + sco + 4))) / 16384.f;
                    sd = float(i16(font->rd16(font->data.data() + sco + 6))) / 16384.f;
                    sco += 8;
                }
                float ca = a * sa + c * sb;
                float cb = b * sa + d * sb;
                float cc = a * sc + c * sd;
                float cd = b * sc + d * sd;
                float cdx = dx + a * float(sdx) + c * float(sdy);
                float cdy = dy + b * float(sdx) + d * float(sdy);
                push_component(sidx, cdx, cdy, ca, cb, cc, cd, ox, oy, out, depth + 1);
                if (!(flags & 0x20)) break;
            }
        }
    }

    void append_simple(u32 off, i16 nc, float ox, float oy, std::vector<Edge>& out, bool unscaled = false) {
        if (nc <= 0) return;
        if (off + 10 + size_t(nc) * 2 > font->data.size()) return;
        const u8* ends = font->data.data() + off + 10;
        u16 npts = u16(font->rd16(ends + size_t(nc - 1) * 2) + 1);
        if (npts == 0) return;
        const u8* ins = ends + size_t(nc) * 2;
        u16 ilen = font->rd16(ins);
        const u8* flags_p = ins + 2 + ilen;
        if (flags_p + npts > font->data.data() + font->data.size()) return;
        std::vector<u8> fl(npts);
        size_t fp = 0;
        u16 rep = 0;
        u8 cur = 0;
        for (u16 i = 0; i < npts; i++) {
            if (rep > 0) { rep--; fl[i] = cur; }
            else {
                cur = flags_p[fp++];
                fl[i] = cur;
                if (cur & 8) { rep = flags_p[fp++]; }
            }
        }
        std::vector<float> px(npts), py(npts);
        size_t cp2 = fp;
        i32 x = 0;
        for (u16 i = 0; i < npts; i++) {
            u8 f = fl[i];
            if (f & 2) {
                u8 d = flags_p[cp2++];
                x += (f & 16) ? i32(d) : -i32(d);
            } else if (!(f & 16)) {
                x += i32(i16(font->rd16(flags_p + cp2)));
                cp2 += 2;
            }
            px[i] = unscaled ? float(x) : x * scale + ox;
        }
        i32 y = 0;
        for (u16 i = 0; i < npts; i++) {
            u8 f = fl[i];
            if (f & 4) {
                u8 d = flags_p[cp2++];
                y += (f & 32) ? i32(d) : -i32(d);
            } else if (!(f & 32)) {
                y += i32(i16(font->rd16(flags_p + cp2)));
                cp2 += 2;
            }
            py[i] = unscaled ? float(y) : -y * scale + oy;
        }
        u16 start = 0;
        for (int c = 0; c < nc; c++) {
            u16 end = font->rd16(ends + size_t(c) * 2);
            if (end >= npts || end < start) break;
            int m = int(end - start + 1);
            int s0 = -1;
            for (int i = 0; i < m; i++) {
                if (fl[start + i] & 1) { s0 = i; break; }
            }
            float sx, sy;
            int it, total;
            if (s0 < 0) {
                int pA = start, pB = start + m - 1;
                sx = 0.5f * (px[pA] + px[pB]);
                sy = 0.5f * (py[pA] + py[pB]);
                it = 0;
                total = m + 1;
            } else {
                sx = px[start + s0];
                sy = py[start + s0];
                it = 1;
                total = m + 1;
            }
            float lx = sx, ly = sy;
            int idx = s0 < 0 ? 0 : (s0 + it) % m;
            int consumed = s0 < 0 ? 0 : it;
            while (consumed < total) {
                int p = start + idx % m;
                bool onc = (fl[p] & 1) != 0;
                float cx = px[p], cy = py[p];
                if (onc) {
                    emit_line(lx, ly, cx, cy, out);
                    lx = cx; ly = cy;
                    consumed++;
                    idx = (idx + 1) % m;
                } else {
                    int np = start + (idx + 1) % m;
                    bool nonc = (fl[np] & 1) != 0;
                    float nx = px[np], ny = py[np];
                    float qx, qy;
                    if (nonc) {
                        qx = nx; qy = ny;
                        consumed += 2;
                    } else {
                        qx = 0.5f * (cx + nx);
                        qy = 0.5f * (cy + ny);
                        consumed += 1;
                    }
                    emit_quad(lx, ly, cx, cy, qx, qy, out);
                    lx = qx; ly = qy;
                    idx = (idx + (nonc ? 2 : 1)) % m;
                }
            }
            emit_line(lx, ly, sx, sy, out);
            start = end + 1;
        }
    }

    static void emit_line(float x0, float y0, float x1, float y1, std::vector<Edge>& out) {
        if (y0 == y1) return;
        out.push_back({x0, y0, x1, y1});
    }

    static void emit_quad(float x0, float y0, float cx, float cy, float x1, float y1, std::vector<Edge>& out) {
        int steps = 6;
        float lx = x0, ly = y0;
        for (int i = 1; i <= steps; i++) {
            float t = float(i) / steps;
            float a = (1 - t) * (1 - t);
            float b = 2 * (1 - t) * t;
            float c = t * t;
            float nx = a * x0 + b * cx + c * x1;
            float ny = a * y0 + b * cy + c * y1;
            emit_line(lx, ly, nx, ny, out);
            lx = nx; ly = ny;
        }
    }

    const GlyphBitmap& get(u32 cp, float px) {
        u64 k = key(cp, px);
        auto it = cache.find(k);
        if (it != cache.end()) return it->second;
        set_size(px);
        GlyphBitmap g;
        g.valid = false;
        g.advance = 0;
        g.w = g.h = 0;
        g.bearing_x = g.bearing_y = 0;
        g.atlas_x = g.atlas_y = g.page = 0;
        Font* use = font;
        u16 gid = use ? use->map_codepoint(cp) : 0;
        if (!gid && fallback) {
            use = fallback;
            gid = use->map_codepoint(cp);
        }
        if (use && gid) {
            scale = px / float(use->units_per_em);
            u32 len = 0;
            u32 off = use->glyph_offset(gid, &len);
            float adv = use->advance_of(gid) * (px / float(use->units_per_em));
            g.advance = adv;
            if (len > 0 && off + 10 <= use->data.size()) {
                std::vector<Edge> edges;
                contour_edges_with(gid, 0.f, 0.f, edges, use);
                if (!edges.empty()) {
                    float minx = edges[0].x0, maxx = edges[0].x0;
                    float miny = edges[0].y0, maxy = edges[0].y0;
                    for (const Edge& e : edges) {
                        minx = std::min(minx, std::min(e.x0, e.x1));
                        maxx = std::max(maxx, std::max(e.x0, e.x1));
                        miny = std::min(miny, std::min(e.y0, e.y1));
                        maxy = std::max(maxy, std::max(e.y0, e.y1));
                    }
                    int x0 = int(floor(minx));
                    int x1 = int(ceil(maxx));
                    int y0 = int(floor(miny));
                    int y1 = int(ceil(maxy));
                    int gw = x1 - x0 + 1;
                    int gh = y1 - y0 + 1;
                    if (gw > 0 && gh > 0 && gw < 512 && gh < 512) {
                        for (Edge& e : edges) {
                            e.x0 += -float(x0);
                            e.x1 += -float(x0);
                            e.y0 += float(-y0);
                            e.y1 += float(-y0);
                        }
                        g.cov.assign(size_t(gw) * gh, 0);
                        rasterize(edges, gw, gh, g.cov);
                        g.w = gw;
                        g.h = gh;
                        g.bearing_x = x0;
                        g.bearing_y = -y0;
                        g.valid = true;
                    }
                }
            }
        }
        auto res = cache.emplace(k, std::move(g));
        return res.first->second;
    }

    void contour_edges_with(u16 gid, float ox, float oy, std::vector<Edge>& out, Font* use) {
        Font* save = font;
        font = use;
        u32 len = 0;
        u32 off = font->glyph_offset(gid, &len);
        if (len == 0) { font = save; return; }
        i16 nc = font->rdi16(font->data.data() + off);
        if (nc >= 0) {
            append_simple(off, nc, ox, oy, out);
        } else {
            u32 co = off + 10;
            while (co + 4 <= off + len) {
                u16 flags = font->rd16(font->data.data() + co);
                u16 idx = font->rd16(font->data.data() + co + 2);
                co += 4;
                i32 dx = 0, dy = 0;
                if (flags & 1) {
                    dx = font->rdi16(font->data.data() + co);
                    dy = font->rdi16(font->data.data() + co + 2);
                    co += 4;
                } else {
                    dx = i8(font->data[co]);
                    dy = i8(font->data[co + 1]);
                    co += 2;
                }
                float a = 1, b = 0, c = 0, d = 1;
                if (flags & 8) { a = float(i16(font->rd16(font->data.data() + co))) / 16384.f; co += 2; }
                else if (flags & 0x40) {
                    a = float(i16(font->rd16(font->data.data() + co))) / 16384.f;
                    d = float(i16(font->rd16(font->data.data() + co + 2))) / 16384.f;
                    co += 4;
                } else if (flags & 0x80) {
                    a = float(i16(font->rd16(font->data.data() + co))) / 16384.f;
                    b = float(i16(font->rd16(font->data.data() + co + 2))) / 16384.f;
                    c = float(i16(font->rd16(font->data.data() + co + 4))) / 16384.f;
                    d = float(i16(font->rd16(font->data.data() + co + 6))) / 16384.f;
                    co += 8;
                }
                push_component(idx, float(dx), float(dy), a, b, c, d, ox, oy, out, 0);
                if (!(flags & 0x20)) break;
            }
        }
        font = save;
    }

    static void rasterize(const std::vector<Edge>& edges, int w, int h, std::vector<u8>& cov) {
        const int SS = 4;
        float ss = 1.f / SS;
        for (int py = 0; py < h; py++) {
            for (int px = 0; px < w; px++) {
                int hit = 0;
                for (int syi = 0; syi < SS; syi++) {
                    float sy = float(py) + (syi + 0.5f) * ss;
                    for (int sxi = 0; sxi < SS; sxi++) {
                        float sx = float(px) + (sxi + 0.5f) * ss;
                        int winding = 0;
                        for (const Edge& e : edges) {
                            float ymin = e.y0 < e.y1 ? e.y0 : e.y1;
                            float ymax = e.y0 < e.y1 ? e.y1 : e.y0;
                            if (sy < ymin || sy >= ymax) continue;
                            float t = (sy - e.y0) / (e.y1 - e.y0);
                            float xx = e.x0 + t * (e.x1 - e.x0);
                            if (xx < sx) {
                                winding += (e.y1 > e.y0) ? 1 : -1;
                            }
                        }
                        if (winding != 0) hit++;
                    }
                }
                cov[size_t(py) * w + px] = u8(hit * 255 / (SS * SS));
            }
        }
    }
};

}

}



#ifdef __ANDROID__

namespace wa {

namespace glr {

struct TexItem {
    int slot;
    Bytes data;
    int w, h;
};

struct Ctx {
    EGLDisplay display = EGL_NO_DISPLAY;
    EGLSurface surface = EGL_NO_SURFACE;
    EGLContext context = EGL_NO_CONTEXT;
    ANativeWindow* win = nullptr;
    u32 prog_shape = 0, prog_tex = 0, prog_text = 0, prog_icon = 0;
    u32 vbo = 0, vbo_tex = 0, vbo_text = 0;
    u32 ls_tex = 0, btn_tex[4] = {0, 0, 0, 0};
    int ls_w = 0, ls_h = 0;
    int btn_w[4] = {0, 0, 0, 0}, btn_h[4] = {0, 0, 0, 0};
    int vw = 0, vh = 0;
    float density = 2.f;
    std::mutex tex_mu;
    std::vector<TexItem> tex_queue;
    GLint u_shape_mvp, u_shape_res, u_shape_dp, u_shape_time, u_shape_home;
    GLint u_icon_mvp, u_icon_sampler;
    GLint u_tex_mvp, u_tex_sampler;
    GLint u_text_mvp, u_text_sampler;
    GLint a_shape_pos, a_shape_rect, a_shape_rad, a_shape_col, a_shape_brd;
    GLint a_tex_pos, a_tex_uv, a_tex_col;
    GLint a_text_pos, a_text_uv, a_text_col;
};

static const char* VS_SHAPE = R"(#version 300 es
uniform mat4 u_mvp;
layout(location=0) in vec2 a_pos;
layout(location=1) in vec4 a_rect;
layout(location=2) in vec4 a_par;
layout(location=3) in vec4 a_c0;
layout(location=4) in vec4 a_c1;
layout(location=5) in vec4 a_brd;
layout(location=6) in vec4 a_ex;
flat out vec4 v_rect;
flat out vec4 v_par;
flat out vec4 v_c0;
flat out vec4 v_c1;
flat out vec4 v_brd;
flat out vec4 v_ex;
void main() {
    gl_Position = u_mvp * vec4(a_pos, 0.0, 1.0);
    v_rect = a_rect;
    v_par = a_par;
    v_c0 = a_c0;
    v_c1 = a_c1;
    v_brd = a_brd;
    v_ex = a_ex;
})";

static const char* FS_SHAPE = R"(#version 300 es
precision highp float;
uniform vec2 u_res;
uniform float u_dp;
uniform float u_time;
uniform float u_home;
flat in vec4 v_rect;
flat in vec4 v_par;
flat in vec4 v_c0;
flat in vec4 v_c1;
flat in vec4 v_brd;
flat in vec4 v_ex;
out vec4 frag;

float sd_rbox(vec2 p, vec2 b, float r) {
    vec2 q = abs(p) - b + r;
    return length(max(q, 0.0)) + min(max(q.x, q.y), 0.0) - r;
}

float sd_ell(vec2 p, vec2 r) {
    vec2 rr = max(r, vec2(0.001));
    return (length(p / rr) - 1.0) * min(rr.x, rr.y);
}

float hash21(vec2 p) {
    p = fract(p * vec2(123.34, 456.21));
    p += dot(p, p + 45.32);
    return fract(p.x * p.y);
}

float sq(float x) {
    return x * x;
}

float band(float x, float w) {
    return 1.0 - smoothstep(0.0, w, abs(x));
}

vec4 emit(vec3 l, float va) {
    float m = clamp(max(l.r, max(l.g, l.b)), 0.0, 1.0);
    float a = max(m, clamp(va, 0.0, 1.0));
    return vec4(min(l, vec3(a)), a);
}

vec3 hexgrid(vec2 uv) {
    vec2 r = vec2(1.0, 1.7320508);
    vec2 h = r * 0.5;
    vec2 a = mod(uv, r) - h;
    vec2 b = mod(uv - h, r) - h;
    vec2 gv = dot(a, a) < dot(b, b) ? a : b;
    vec2 id = uv - gv;
    float d = max(dot(abs(gv), vec2(0.5, 0.8660254)), abs(gv.x));
    return vec3(0.5 - d, id);
}

vec4 background(vec2 f) {
    vec2 R = u_res / u_dp;
    vec2 uv = f / R;
    float t = u_time;
    float asp = R.x / R.y;
    float k = 0.35 + 0.65 * u_home;
    vec2 p = (uv - vec2(0.5, 0.55)) * vec2(asp, 1.0);
    float r = length(p);
    vec3 L = vec3(0.0);
    float va = 0.0;
    float pulse = 0.85 + 0.15 * sin(t * 1.7);

    L += vec3(0.5, 0.36, 0.04) * exp(-r * r * 5.0) * 0.17 * pulse;
    L += vec3(0.95, 0.76, 0.2) * exp(-sq((r - 0.34) * 30.0)) * 0.08 * pulse;

    float ang = atan(p.y, p.x);
    float turns = ang / 6.2831853;
    float ring1 = band(r - 0.335, 0.0030);
    float tickMask = step(0.80, fract((turns + t * 0.010) * 120.0));
    float ring2 = band(r - 0.352, 0.0060) * tickMask;
    float longT = step(0.93, fract((turns + t * 0.010) * 24.0));
    float ring3 = band(r - 0.362, 0.0110) * longT;
    float dash = step(0.5, fract((turns - t * 0.02) * 10.0)) * band(r - 0.305, 0.0022);
    float arcs = step(0.0, sin(ang * 2.0 + t * 0.7)) * band(r - 0.378, 0.0030);
    float inner = band(r - 0.25, 0.0016) * step(0.35, fract((turns + t * 0.03) * 6.0));
    L += vec3(1.0, 0.78, 0.3) * (ring1 * 0.35 + ring2 * 0.45 + ring3 * 0.55 + dash * 0.35 + arcs * 0.5 + inner * 0.25);

    float fy = max(uv.y - 0.70, 0.002);
    vec2 g = vec2((uv.x - 0.5) * asp / fy * 1.35, 0.06 / fy * 5.0 - t * 0.9);
    vec2 gd = abs(fract(g) - 0.5);
    vec2 gw = fwidth(g);
    vec2 gl = 1.0 - smoothstep(vec2(0.0), gw * 1.6 + vec2(0.001), vec2(0.5) - gd);
    float gline = max(gl.x, gl.y);
    float gfade = smoothstep(0.0, 0.18, fy) * (1.0 - 0.35 * smoothstep(0.1, 0.3, fy));
    float cmask = 0.30 + 0.70 * smoothstep(0.0, 0.40, abs(uv.x - 0.5));
    L += vec3(0.95, 0.72, 0.16) * gline * gfade * cmask * step(0.70, uv.y) * 0.50;
    L += vec3(0.95, 0.73, 0.16) * exp(-sq((uv.y - 0.70) * 22.0)) * (0.10 + 0.08 * pulse) * (1.0 - 0.6 * smoothstep(0.1, 0.5, abs(uv.x - 0.5)));

    for (int i = 0; i < 3; i++) {
        float fi = float(i);
        float x0 = (0.16 + fi * 0.34 + 0.04 * sin(t * 0.4 + fi * 2.1)) * asp;
        float a0 = 0.32 - fi * 0.30 + 0.05 * sin(t * 0.3 + fi);
        vec2 dir = vec2(sin(a0), cos(a0));
        vec2 q = uv * vec2(asp, 1.0) - vec2(x0, 0.0);
        float along = dot(q, dir);
        float across = dot(q, vec2(dir.y, -dir.x));
        float w = 0.025 + 0.11 * max(along, 0.0);
        float bm = exp(-across * across / (w * w)) * smoothstep(-0.05, 0.15, along) * exp(-along * 1.5);
        vec3 bc = mix(vec3(0.75, 0.55, 0.1), vec3(0.30, 0.42, 0.75), float(i == 1));
        L += bc * bm * 0.11;
    }

    float side = smoothstep(0.28, 0.46, abs(uv.x - 0.5));
    if (side > 0.01) {
        vec3 hx = hexgrid(f / 20.0);
        float ln = 1.0 - smoothstep(0.0, 0.06, hx.x);
        float hr = hash21(hx.yz);
        float flash = step(0.90, hr) * (0.5 + 0.5 * sin(t * 2.0 + hr * 60.0));
        float wave = 0.55 + 0.45 * sin(length(f / 20.0) * 0.35 - t * 1.5);
        L += vec3(0.95, 0.74, 0.18) * (ln * 0.16 * wave + flash * 0.10 * step(0.0, hx.x)) * side;
    }

    float edge = step(f.y, 5.0) + step(R.y - 5.0, f.y);
    float st = step(0.5, fract((f.x + f.y) / 9.0));
    L += vec3(0.9, 0.68, 0.14) * edge * st * 0.55;

    float dxr = (R.x - 10.0) - f.x;
    float major = step(mod(f.y, 30.0), 1.0);
    float tlen = mix(3.5, 7.0, major);
    float tick = step(0.0, dxr) * step(dxr, tlen) * step(mod(f.y, 6.0), 1.0);
    float mk = exp(-sq((f.y - fract(t * 0.07) * R.y) / 7.0)) * step(abs(dxr), 8.0);
    L += vec3(1.0, 0.8, 0.32) * (tick * 0.30 + mk * 0.55);

    float sb = exp(-sq((uv.y - fract(t * 0.08)) * 12.0));
    L += vec3(0.30, 0.40, 0.55) * sb * 0.05;
    L += vec3(0.6, 0.44, 0.05) * exp(-dot(uv - vec2(1.0, 0.0), uv - vec2(1.0, 0.0)) * 7.0) * 0.16;
    L += vec3(0.20, 0.28, 0.55) * exp(-dot(uv - vec2(0.0, 1.0), uv - vec2(0.0, 1.0)) * 8.0) * 0.12;

    va += 0.07 * (0.5 + 0.5 * sin(f.y * 2.6));
    float v = length((uv - 0.5) * vec2(1.25, 1.0));
    float vig = smoothstep(0.45, 1.0, v);
    va += vig * 0.78;
    L += vec3(0.45, 0.32, 0.02) * vig * vig * 0.45 * (0.8 + 0.2 * sin(t * 2.0));

    float gn = hash21(gl_FragCoord.xy + vec2(fract(t) * 91.7, fract(t * 1.7) * 37.1));
    L += vec3(max(gn - 0.5, 0.0) * 0.07);

    L *= k * (0.97 + 0.03 * sin(t * 23.0));
    return emit(L, va * (0.6 + 0.4 * k));
}

void main() {
    vec2 f = vec2(gl_FragCoord.x, u_res.y - gl_FragCoord.y) / u_dp;
    int type = int(v_par.y + 0.5);
    if (type == 6) {
        frag = background(f);
        return;
    }
    int fl = int(v_par.w + 0.5);
    bool add = (fl & 2) != 0;
    bool horiz = (fl & 1) != 0;
    vec2 p = f - v_rect.xy;
    vec2 hs = v_rect.zw;
    float rad = v_par.x;
    float bw = v_par.z;
    float aa = 0.75 / u_dp;
    float d;
    if (type == 2 || type == 3 || type == 4) {
        d = sd_rbox(p, hs, 0.0);
        float lim = hs.x + hs.y - rad;
        if (type == 2 || type == 4) d = max(d, (abs(p.x + p.y) - lim) * 0.70711);
        if (type == 3 || type == 4) d = max(d, (abs(p.x - p.y) - lim) * 0.70711);
    } else if (type == 8 || type == 9) {
        d = sd_ell(p, hs);
    } else {
        d = sd_rbox(p, hs, max(rad, 0.0));
    }
    if (type == 1 || type == 9) {
        float s = max(bw, 0.5);
        float x = max(d, 0.0) / s;
        float I = exp(-x * x * 1.6);
        frag = emit(v_c0.rgb * v_c0.a * I, 0.0);
        return;
    }
    float fill = 1.0 - smoothstep(-aa, aa, d);
    float tg = horiz ? (p.x / max(hs.x, 0.001) * 0.5 + 0.5) : (p.y / max(hs.y, 0.001) * 0.5 + 0.5);
    tg = clamp(tg, 0.0, 1.0);
    vec4 col = mix(v_c0, v_c1, tg);
    vec3 rgb = col.rgb;
    if (v_ex.z > 0.0) {
        float sp = step(0.5, fract((p.x - p.y) / 8.0 + u_time * 0.4));
        rgb += vec3(0.3, 0.22, 0.03) * sp * v_ex.z;
    }
    if (v_ex.w > 0.0) {
        rgb *= 1.0 - v_ex.w * (0.5 + 0.5 * sin(f.y * 2.8));
    }
    if (v_ex.y > 0.0) {
        float u2 = (p.x + p.y * 0.5) / (2.0 * max(hs.x, 0.001)) + 0.5;
        float bnd = exp(-sq((u2 - v_ex.x) / v_ex.y));
        rgb += vec3(1.0, 0.93, 0.72) * bnd * 0.45;
    }
    float fa = col.a * fill;
    vec3 pc = rgb * fa;
    float ra = 0.0;
    if (bw > 0.0) {
        float innr = 1.0 - smoothstep(-aa, aa, d + bw);
        ra = clamp(fill - innr, 0.0, 1.0) * v_brd.a;
    }
    vec3 o = pc * (1.0 - ra) + v_brd.rgb * ra;
    float oa = fa * (1.0 - ra) + ra;
    if (add) {
        frag = emit(o, 0.0);
    } else {
        frag = vec4(min(o, vec3(oa)), oa);
    }
})";

static const char* VS_TEX = R"(#version 300 es
uniform mat4 u_mvp;
layout(location=0) in vec2 a_pos;
layout(location=1) in vec2 a_uv;
layout(location=2) in vec4 a_col;
out vec2 v_uv;
out vec4 v_col;
void main() {
    gl_Position = u_mvp * vec4(a_pos, 0.0, 1.0);
    v_uv = a_uv;
    v_col = a_col;
})";

static const char* FS_TEX = R"(#version 300 es
precision mediump float;
uniform sampler2D u_sampler;
in vec2 v_uv;
in vec4 v_col;
out vec4 frag;
void main() {
    vec4 t = texture(u_sampler, v_uv);
    float a = t.a * v_col.a;
    frag = vec4(t.rgb * v_col.rgb * a, a);
})";

static const char* FS_ICON = R"(#version 300 es
precision mediump float;
uniform sampler2D u_sampler;
in vec2 v_uv;
in vec4 v_col;
out vec4 frag;
void main() {
    float a = texture(u_sampler, v_uv).a * v_col.a;
    frag = vec4(v_col.rgb * a, a);
})";

static u32 compile_shader(u32 type, const char* src) {
    u32 s = glCreateShader(type);
    glShaderSource(s, 1, &src, nullptr);
    glCompileShader(s);
    GLint ok = 0;
    glGetShaderiv(s, GL_COMPILE_STATUS, &ok);
    if (!ok) {
        char log[512];
        glGetShaderInfoLog(s, 512, nullptr, log);
        WA_LOG("shader error: %s", log);
        glDeleteShader(s);
        return 0;
    }
    return s;
}

static u32 link_program(const char* vs, const char* fs) {
    u32 v = compile_shader(GL_VERTEX_SHADER, vs);
    u32 f = compile_shader(GL_FRAGMENT_SHADER, fs);
    if (!v || !f) return 0;
    u32 p = glCreateProgram();
    glAttachShader(p, v);
    glAttachShader(p, f);
    glLinkProgram(p);
    GLint ok = 0;
    glGetProgramiv(p, GL_LINK_STATUS, &ok);
    glDeleteShader(v);
    glDeleteShader(f);
    if (!ok) return 0;
    return p;
}

static u32 make_tex_rgba(const u8* px, int w, int h) {
    u32 t = 0;
    glGenTextures(1, &t);
    glBindTexture(GL_TEXTURE_2D, t);
    glPixelStorei(GL_UNPACK_ALIGNMENT, 1);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA8, w, h, 0, GL_RGBA, GL_UNSIGNED_BYTE, px);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
    return t;
}

bool init(Ctx& c, ANativeWindow* win, float density) {
    c.win = win;
    c.density = density;
    c.display = eglGetDisplay(EGL_DEFAULT_DISPLAY);
    if (c.display == EGL_NO_DISPLAY) return false;
    if (!eglInitialize(c.display, nullptr, nullptr)) return false;
    const EGLint cfg_attr[] = {EGL_RENDERABLE_TYPE, EGL_OPENGL_ES3_BIT, EGL_RED_SIZE, 8,
                               EGL_GREEN_SIZE, 8, EGL_BLUE_SIZE, 8, EGL_ALPHA_SIZE, 8,
                               EGL_SURFACE_TYPE, EGL_WINDOW_BIT, EGL_NONE};
    EGLConfig cfg;
    EGLint ncfg = 0;
    if (!eglChooseConfig(c.display, cfg_attr, &cfg, 1, &ncfg) || ncfg < 1) return false;
    const EGLint ctx_attr[] = {EGL_CONTEXT_CLIENT_VERSION, 3, EGL_NONE};
    c.context = eglCreateContext(c.display, cfg, EGL_NO_CONTEXT, ctx_attr);
    if (c.context == EGL_NO_CONTEXT) return false;
    c.surface = eglCreateWindowSurface(c.display, cfg, win, nullptr);
    if (c.surface == EGL_NO_SURFACE) return false;
    if (!eglMakeCurrent(c.display, c.surface, c.surface, c.context)) return false;
    eglQuerySurface(c.display, c.surface, EGL_WIDTH, &c.vw);
    eglQuerySurface(c.display, c.surface, EGL_HEIGHT, &c.vh);
    c.prog_shape = link_program(VS_SHAPE, FS_SHAPE);
    c.prog_tex = link_program(VS_TEX, FS_TEX);
    c.prog_text = link_program(VS_TEX, FS_TEX);
    c.prog_icon = link_program(VS_TEX, FS_ICON);
    if (!c.prog_shape || !c.prog_tex || !c.prog_text || !c.prog_icon) return false;
    c.u_shape_mvp = glGetUniformLocation(c.prog_shape, "u_mvp");
    c.u_shape_res = glGetUniformLocation(c.prog_shape, "u_res");
    c.u_shape_dp = glGetUniformLocation(c.prog_shape, "u_dp");
    c.u_shape_time = glGetUniformLocation(c.prog_shape, "u_time");
    c.u_shape_home = glGetUniformLocation(c.prog_shape, "u_home");
    c.u_icon_mvp = glGetUniformLocation(c.prog_icon, "u_mvp");
    c.u_icon_sampler = glGetUniformLocation(c.prog_icon, "u_sampler");
    c.u_tex_mvp = glGetUniformLocation(c.prog_tex, "u_mvp");
    c.u_tex_sampler = glGetUniformLocation(c.prog_tex, "u_sampler");
    c.u_text_mvp = glGetUniformLocation(c.prog_text, "u_mvp");
    c.u_text_sampler = glGetUniformLocation(c.prog_text, "u_sampler");
    glGenBuffers(1, &c.vbo);
    glGenBuffers(1, &c.vbo_tex);
    glGenBuffers(1, &c.vbo_text);
    glEnable(GL_BLEND);
    glBlendFuncSeparate(GL_ONE, GL_ONE_MINUS_SRC_ALPHA, GL_ONE, GL_ONE_MINUS_SRC_ALPHA);
    glDisable(GL_DEPTH_TEST);
    return true;
}

void destroy(Ctx& c) {
    if (c.display != EGL_NO_DISPLAY) {
        eglMakeCurrent(c.display, EGL_NO_SURFACE, EGL_NO_SURFACE, EGL_NO_CONTEXT);
        if (c.surface != EGL_NO_SURFACE) eglDestroySurface(c.display, c.surface);
        if (c.context != EGL_NO_CONTEXT) eglDestroyContext(c.display, c.context);
        eglTerminate(c.display);
    }
    c.display = EGL_NO_DISPLAY;
    c.surface = EGL_NO_SURFACE;
    c.context = EGL_NO_CONTEXT;
    if (c.win) {
        ANativeWindow_release(c.win);
        c.win = nullptr;
    }
}

} 

namespace glr {
Ctx gl_ctx;
}

namespace audio {

static void synth_click(std::vector<u8>& pcm, float vol) {
    const int sr = 48000;
    const int dur = int(0.075f * sr);
    pcm.resize(size_t(dur) * 2);
    unsigned rs = 1234567u;
    for (int i = 0; i < dur; i++) {
        float t = float(i) / sr;
        float env1 = expf(-t * 55.f);
        float f = 1500.f - 820.f * (t / 0.075f);
        float body = sinf(6.2831853f * f * t) * 0.5f * env1;
        rs = rs * 1664525u + 1013904223u;
        float noise = (float(int(rs >> 16) - 32768) / 32768.f);
        float env2 = expf(-t * 320.f);
        float click = noise * 0.34f * env2;
        float thump = sinf(6.2831853f * 300.f * t) * 0.16f * expf(-t * 42.f);
        float v = body + click + thump;
        v = tanhf(v * 1.6f);
        v *= 0.85f * vol;
        i16 s = i16(v * 32767.f);
        pcm[i * 2] = u8(s & 0xFF);
        pcm[i * 2 + 1] = u8((s >> 8) & 0xFF);
    }
}

} 


namespace ui {

enum Page { PAGE_HOME = 0, PAGE_INV, PAGE_CHAT, PAGE_SET };
enum SetTab { TAB_SOUND = 0, TAB_GFX, TAB_MISC };
enum Phase { PHASE_LOADING = 0, PHASE_AUTH = 1, PHASE_MENU = 2 };

struct Strings {
    const char* loading;
    const char* music;
    const char* sfx;
    const char* tab_sound;
    const char* tab_gfx;
    const char* tab_misc;
    const char* language;
    const char* change;
    const char* version;
    const char* inv_msg;
    const char* gfx_msg;
    const char* chat_msg;
    const char* lang_name;
    const char* play;
    const char* soon;
    const char* operative;
    const char* mode_lbl;
    const char* season;
    const char* modes[3];
    const char* tips[3];
    const char* logout;
};

struct SecurityStrings {
    const char* root;
    const char* tamper;
    const char* emulator;
};

static const SecurityStrings SECURITY_STRINGS[3] = {
    {
        "На устройстве обнаружен root-доступ. Root может использоваться для изменения или реверса игры, что запрещено правилами игры. Запустите игру без root-доступа.",
        "Что-то пошло не так...",
        "Игра запущена в Windows-эмуляторе Android. У игры есть отдельная Windows-версия, поэтому игра в Windows-эмуляторах запрещена по соображениям безопасности."
    },
    {
        "Your device is rooted. Root access can be used to modify or reverse the game, which is prohibited by the game rules. Launch the game without root access.",
        "Something went wrong...",
        "The game runs on a Windows Android emulator. The game has a separate Windows version, so playing on Windows emulators is prohibited for security reasons."
    },
    {
        "Cihazınızda root erişimi algılandı. Root erişimi oyunu değiştirmek veya tersine mühendislik yapmak için kullanılabilir ve bu durum oyun kurallarına aykırıdır. Oyunu root erişimi olmadan başlatın.",
        "Bir şeyler ters gitti...",
        "Oyun bir Windows Android emülatöründe çalışıyor. Oyunun ayrı bir Windows sürümü vardır; güvenlik nedeniyle Windows emülatörlerinde oynamak yasaktır."
    }
};

static const Strings STRINGS[3] = {
    {"Загрузка: ", "Музыка", "Звуки", "Звук", "Графика", "Прочее", "Язык", "Изменить", "Версия",
     "ИНВЕНТАРЬ В РАЗРАБОТКЕ",
     "ИГРОВАЯ ЛОГИКА ЕЩЁ НЕ НАПИСАНА, ГРАФИКА В РАЗРАБОТКЕ",
     "ЧАТ В РАЗРАБОТКЕ", "Русский",
     "ИГРАТЬ", "В РАЗРАБОТКЕ", "", "РЕЖИМ", "СЕЗОН",
     {"ТРОИЦА", "ПРОТИВ ВСЕХ", "ОБЕЗВРЕЖИВАНИЕ"},
     {"ЦЕЛЬТЕСЬ В ГОЛОВУ", "МЕНЯЙТЕ ПОЗИЦИЮ ПОСЛЕ КАЖДОГО УБИЙСТВА", "СЛУШАЙТЕ ШАГИ И ДЕРЖИТЕ УГОЛ"},
     "ВЫЙТИ"},
    {"Loading: ", "Music", "Sound FX", "Sound", "Graphics", "Misc", "Language", "Change", "Version",
     "INVENTORY IS UNDER DEVELOPMENT",
     "GAME LOGIC HAS NOT BEEN WRITTEN YET, GRAPHICS ARE IN DEVELOPMENT",
     "CHAT IS UNDER DEVELOPMENT", "English",
     "PLAY", "IN DEVELOPMENT", "", "MODE", "SEASON",
     {"TRINITY", "FREE FOR ALL", "DEFUSAL"},
     {"AIM FOR THE HEAD", "CHANGE POSITION AFTER EVERY KILL", "LISTEN FOR FOOTSTEPS AND HOLD THE ANGLE"},
     "LOG OUT"},
    {"Yükleniyor: ", "Müzik", "Sesler", "Ses", "Grafik", "Diğer", "Dil", "Değiştir", "Sürüm",
     "ENVANTER GELİŞTİRİLİYOR",
     "OYUN MANTIĞI HENÜZ YAZILMADI, GRAFİKLER GELİŞTİRİLİYOR",
     "SOHBET GELİŞTİRİLİYOR", "Türkçe",
     "OYNA", "GELİŞTİRİLİYOR", "", "MOD", "SEZON",
     {"ÜÇLÜ", "HERKESE KARŞI", "ETKİSİZLEŞTİRME"},
     {"KAFAYA NİŞAN AL", "HER ÖLDÜRMEDEN SONRA YER DEĞİŞTİR", "ADIM SESLERİNİ DİNLE"},
     "ÇIKIŞ YAP"},
};

struct Rect {
    float x, y, w, h;
    bool hit(float px, float py) const { return px >= x && px <= x + w && py >= y && py <= y + h; }
};

struct Slider {
    Rect track;
    float value = 0.5f;
    bool dragging = false;
};

struct App {
    int phase = PHASE_LOADING;
    Page page = PAGE_HOME;
    SetTab tab = TAB_SOUND;
    int lang = 1;
    float progress = 0.f;
    float shown_progress = 0.f;
    float music_vol = 0.8f;
    float sfx_vol = 0.8f;
    bool music_ready = false;
    float fade_in = 0.f;
    float fade_out = 0.f;
    float page_anim = 1.f;
    float home_mix = 1.f;
    int prev_page = 0;
    float time = 0.f;
    float press_tile = -1.f;
    float press_tile_t = 0.f;
    int press_tab = -1;
    float press_tab_t = 0.f;
    bool press_change = false;
    float press_change_t = 0.f;
    bool press_tg = false;
    float press_tg_t = 0.f;
    Slider music_sl, sfx_sl;
    Rect tile_rects[4];
    Rect tab_rects[3];
    Rect change_rect, tg_rect;
    int vw = 0, vh = 0;
    float dp = 2.f;
    std::string version = "0.1.0";
    bool menu_entered = false;
    bool finished = false;
    float intro = 0.f;
    int mode = 0;
    int mode_dir = 1;
    float mode_anim = 1.f;
    int press_btn = -1;
    float press_btn_t = 0.f;
    float toast = 0.f;
    float lp_x = 0.f, lp_w = 0.f, rp_x = 0.f, rp_w = 0.f;
    Rect play_rect, mode_l, mode_r;
    Rect logout_rect;
    bool press_logout = false;
    float press_logout_t = 0.f;
    bool auth_ready = false;
    bool session_valid = false;
};

static App app;

struct DrawList {
    std::vector<float> shape;
    std::vector<float> textured;
    std::vector<float> textv;
    struct Item { int prog; int tex; int first; int count; };
    std::vector<Item> items;
    void clear() { shape.clear(); textured.clear(); textv.clear(); items.clear(); }
};

static DrawList dl;

struct Col { float r, g, b, a; };

static const Col K_NONE = {0.f, 0.f, 0.f, 0.f};
static const Col K_GOLD = {0.96f, 0.76f, 0.2f, 1.f};
static const Col K_HOT = {1.f, 0.86f, 0.38f, 1.f};
static const Col K_DEEP = {0.6f, 0.42f, 0.06f, 1.f};
static const Col K_WHITE = {0.95f, 0.93f, 0.91f, 1.f};
static const Col K_GREY = {0.62f, 0.60f, 0.60f, 1.f};

static Col cmk(float r, float g, float b, float a) { return Col{r, g, b, a}; }
static Col cfade(Col c, float a) { c.a *= a; return c; }

static void push_fx(int type, float cx, float cy, float hw, float hh, float pad, float rad, float bw, int flags,
                    Col c0, Col c1, Col b, float e0 = 0.f, float e1 = 0.f, float e2 = 0.f, float e3 = 0.f) {
    float x0 = cx - hw - pad, y0 = cy - hh - pad, x1 = cx + hw + pad, y1 = cy + hh + pad;
    float px[4][2] = {{x0, y0}, {x1, y0}, {x1, y1}, {x0, y1}};
    u16 idx[6] = {0, 1, 2, 0, 2, 3};
    for (int i = 0; i < 6; i++) {
        float* v = px[idx[i]];
        float vert[26] = {v[0], v[1], cx, cy, hw, hh, rad, float(type), bw, float(flags),
                          c0.r, c0.g, c0.b, c0.a, c1.r, c1.g, c1.b, c1.a, b.r, b.g, b.b, b.a, e0, e1, e2, e3};
        dl.shape.insert(dl.shape.end(), vert, vert + 26);
    }
    if (!dl.items.empty() && dl.items.back().prog == 0) dl.items.back().count += 6;
    else dl.items.push_back({0, 0, 0, 6});
}

static void push_shape(float x, float y, float w, float h, float r,
                       float cr, float cg, float cb, float ca,
                       float br, float bg, float bb, float bw) {
    float hw = w * 0.5f, hh = h * 0.5f;
    Col c = {cr, cg, cb, ca};
    Col b = {br, bg, bb, bw < 1.f ? bw : 1.f};
    push_fx(0, x + hw, y + hh, hw, hh, 0.f, r, bw, 0, c, c, b);
}

static void push_tex_quad(u32* cur_tex, int tex, float x, float y, float w, float h,
                          float cr, float cg, float cb, float ca, int prog = 1) {
    if (dl.items.empty() || dl.items.back().prog != prog || dl.items.back().tex != tex) {
        dl.items.push_back({prog, tex, 0, 0});
    }
    float u0 = 0.f, v0 = 0.f, u1 = 1.f, v1 = 1.f;
    float quad[4][8] = {
        {x, y, u0, v0, cr, cg, cb, ca},
        {x + w, y, u1, v0, cr, cg, cb, ca},
        {x + w, y + h, u1, v1, cr, cg, cb, ca},
        {x, y + h, u0, v1, cr, cg, cb, ca}};
    u16 idx[6] = {0, 1, 2, 0, 2, 3};
    for (int i = 0; i < 6; i++) {
        dl.textured.insert(dl.textured.end(), quad[idx[i]], quad[idx[i]] + 8);
    }
    dl.items.back().count += 6;
}

static void push_text_glyph(u32* cur_tex, int tex, float x, float y, float w, float h,
                            float u0, float v0, float u1, float v1,
                            float cr, float cg, float cb, float ca) {
    if (dl.items.empty() || dl.items.back().prog != 2 || dl.items.back().tex != tex) {
        dl.items.push_back({2, tex, 0, 0});
    }
    float quad[4][8] = {
        {x, y, u0, v0, cr, cg, cb, ca},
        {x + w, y, u1, v0, cr, cg, cb, ca},
        {x + w, y + h, u1, v1, cr, cg, cb, ca},
        {x, y + h, u0, v1, cr, cg, cb, ca}};
    u16 idx[6] = {0, 1, 2, 0, 2, 3};
    for (int i = 0; i < 6; i++) {
        dl.textv.insert(dl.textv.end(), quad[idx[i]], quad[idx[i]] + 8);
    }
    dl.items.back().count += 6;
}

struct TextRenderer {
    fontx::Raster title_ras, body_ras;
    fontx::Font title_font, fallback_font, ru_font, tr_font;
    bool title_ok = false, fallback_ok = false, ru_ok = false, tr_ok = false;
    int cur_lang = -1;
    struct AtlasPage {
        u32 tex = 0;
        int x = 1, y = 1, rowh = 0;
    };
    std::vector<AtlasPage> pages;
    struct Placed {
        int page, ax, ay;
    };
    std::unordered_map<const void*, Placed> placed;
    glr::Ctx* gl = nullptr;

    bool load(glr::Ctx* g, const u8* title_data, size_t title_len,
              const u8* ru_data, size_t ru_len, const u8* tr_data, size_t tr_len) {
        gl = g;
        title_ok = title_len > 0 && title_font.init(title_data, title_len);
        ru_ok = ru_len > 0 && ru_font.init(ru_data, ru_len);
        tr_ok = tr_len > 0 && tr_font.init(tr_data, tr_len);
        static const char* cands[] = {"/system/fonts/Roboto-Regular.ttf", "/system/fonts/Roboto-Medium.ttf",
                                      "/system/fonts/NotoSans-Regular.ttf", "/system/fonts/DroidSans.ttf"};
        for (const char* p : cands) {
            FILE* f = fopen(p, "rb");
            if (!f) continue;
            std::vector<u8> buf;
            fseek(f, 0, SEEK_END);
            long n = ftell(f);
            fseek(f, 0, SEEK_SET);
            buf.resize(size_t(n));
            if (fread(buf.data(), 1, buf.size(), f) == buf.size()) fallback_ok = fallback_font.init(buf.data(), buf.size());
            fclose(f);
            if (fallback_ok) break;
        }
        set_lang(cur_lang < 0 ? 0 : cur_lang);
        return title_ok || fallback_ok || ru_ok || tr_ok;
    }

    void set_lang(int lang) {
        cur_lang = lang;
        fontx::Font* lf = nullptr;
        if (lang == 0 && ru_ok) lf = &ru_font;
        else if (lang == 2 && tr_ok) lf = &tr_font;
        else if (lang == 1 && title_ok) lf = &title_font;
        if (!lf) lf = fallback_ok ? &fallback_font : (title_ok ? &title_font : (ru_ok ? &ru_font : &tr_font));
        fontx::Font* alt = nullptr;
        if (lf != &title_font && title_ok) alt = &title_font;
        else if (fallback_ok && lf != &fallback_font) alt = &fallback_font;
        else if (ru_ok && lf != &ru_font) alt = &ru_font;
        title_ras.cache.clear();
        body_ras.cache.clear();
        placed.clear();
        for (AtlasPage& pg : pages) {
            pg.x = 1;
            pg.y = 1;
            pg.rowh = 0;
        }
        title_ras.font = title_ok ? &title_font : lf;
        title_ras.fallback = title_ok ? lf : alt;
        if (title_ras.fallback == title_ras.font) title_ras.fallback = nullptr;
        body_ras.font = lf;
        body_ras.fallback = alt;
    }

    u32 page_tex(int p) {
        while (int(pages.size()) <= p) pages.push_back(AtlasPage());
        if (pages[p].tex == 0) {
            u8* zeros = new u8[1024 * 1024 * 4];
            memset(zeros, 0, size_t(1024) * 1024 * 4);
            pages[p].tex = glr::make_tex_rgba(zeros, 1024, 1024);
            delete[] zeros;
        }
        return pages[p].tex;
    }

    Placed& place(const fontx::GlyphBitmap& g) {
        const void* k = &g;
        auto it = placed.find(k);
        if (it != placed.end()) return it->second;
        int p = 0;
        if (pages.empty()) page_tex(0);
        while (true) {
            AtlasPage& pg = pages[p];
            if (pg.x + g.w + 1 > 1024) {
                pg.x = 1;
                pg.y += pg.rowh + 1;
                pg.rowh = 0;
            }
            if (pg.y + g.h + 1 <= 1024) break;
            p++;
            page_tex(p);
        }
        AtlasPage& pg = pages[p];
        glBindTexture(GL_TEXTURE_2D, pg.tex);
        glPixelStorei(GL_UNPACK_ALIGNMENT, 1);
        std::vector<u8> rgba(size_t(g.w) * g.h * 4, 0);
        for (int i = 0; i < g.w * g.h; i++) {
            rgba[size_t(i) * 4 + 0] = 255;
            rgba[size_t(i) * 4 + 1] = 255;
            rgba[size_t(i) * 4 + 2] = 255;
            rgba[size_t(i) * 4 + 3] = g.cov[i];
        }
        glTexSubImage2D(GL_TEXTURE_2D, 0, pg.x, pg.y, g.w, g.h, GL_RGBA, GL_UNSIGNED_BYTE, rgba.data());
        Placed pl{p, pg.x, pg.y};
        pg.x += g.w + 1;
        if (g.h > pg.rowh) pg.rowh = g.h;
        auto res = placed.emplace(k, pl);
        return res.first->second;
    }

    void draw_text(float x, float y, const std::string& s, float px_size, float ls,
                   float cr, float cg, float cb, float ca, bool title_style = false) {
        fontx::Raster& ras = title_style ? title_ras : body_ras;
        std::u32string cps;
        size_t i = 0;
        while (i < s.size()) {
            u8 c = u8(s[i]);
            u32 cp = c;
            int extra = 0;
            if (c >= 0xF0) { cp = c & 7; extra = 3; }
            else if (c >= 0xE0) { cp = c & 15; extra = 2; }
            else if (c >= 0xC0) { cp = c & 31; extra = 1; }
            for (int e = 0; e < extra && i + 1 + e < s.size(); e++) cp = (cp << 6) | (u8(s[i + 1 + e]) & 63);
            i += 1 + extra;
            cps.push_back(cp);
        }
        float pen = x;
        for (u32 cp : cps) {
            const fontx::GlyphBitmap& g = ras.get(cp, px_size * app.dp);
            if (g.valid) {
                Placed& pl = place(g);
                float w = float(g.w) / app.dp;
                float h = float(g.h) / app.dp;
                float gx = pen + float(g.bearing_x) / app.dp;
                float gy = y - float(g.bearing_y) / app.dp;
                float u0 = (float(pl.ax) + 0.5f) / 1024.f;
                float v0 = (float(pl.ay) + 0.5f) / 1024.f;
                float u1 = (float(pl.ax + g.w) - 0.5f) / 1024.f;
                float v1 = (float(pl.ay + g.h) - 0.5f) / 1024.f;
                push_text_glyph(nullptr, pl.page, gx, gy, w, h, u0, v0, u1, v1, cr, cg, cb, ca);
            }
            pen += g.advance / app.dp + ls;
        }
    }

    float measure(const std::string& s, float px_size, float ls, bool title_style = false) {
        fontx::Raster& ras = title_style ? title_ras : body_ras;
        std::u32string cps;
        size_t i = 0;
        while (i < s.size()) {
            u8 c = u8(s[i]);
            u32 cp = c;
            int extra = 0;
            if (c >= 0xF0) { cp = c & 7; extra = 3; }
            else if (c >= 0xE0) { cp = c & 15; extra = 2; }
            else if (c >= 0xC0) { cp = c & 31; extra = 1; }
            for (int e = 0; e < extra && i + 1 + e < s.size(); e++) cp = (cp << 6) | (u8(s[i + 1 + e]) & 63);
            i += 1 + extra;
            cps.push_back(cp);
        }
        float wsum = 0;
        for (u32 cp : cps) {
            const fontx::GlyphBitmap& g = ras.get(cp, px_size * app.dp);
            wsum += g.advance / app.dp + ls;
        }
        return wsum > 0 ? wsum - ls : 0;
    }
};

static TextRenderer tr;

static std::function<void()> auth_cb_show;
static std::function<void()> auth_cb_hide;
static std::function<void()> auth_cb_start_music;
static std::function<void()> auth_cb_stop_music;
static std::function<void()> auth_cb_logout;
static std::function<void()> request_exit_cb;

static void ui_show_auth_request() { if (auth_cb_show) auth_cb_show(); }
static void ui_hide_auth_request() { if (auth_cb_hide) auth_cb_hide(); }
static void ui_start_music_request() { if (auth_cb_start_music) auth_cb_start_music(); }
static void ui_stop_music_request() { if (auth_cb_stop_music) auth_cb_stop_music(); }
static void ui_logout_request() { if (auth_cb_logout) auth_cb_logout(); }

static void layout() {
    float dp = app.dp;
    int W = app.vw, H = app.vh;
    float Wd = float(W) / dp, Hd = float(H) / dp;
    float tile = 56, gap = 12;
    float total = tile * 4 + gap * 3;
    float ty = (Hd - total) * 0.5f;
    for (int i = 0; i < 4; i++) {
        app.tile_rects[i] = {14, ty + float(i) * (tile + gap), tile, tile};
    }
    float panel_x = 14 + tile + 24;
    float pw = Wd - panel_x - 18;
    for (int i = 0; i < 3; i++) {
        float tw = 86;
        app.tab_rects[i] = {panel_x + float(i) * (tw + 10), 20, tw, 34};
    }
    app.change_rect = {panel_x + 190, 64, 96, 32};
    app.tg_rect = {panel_x + 14, 118, 40, 40};
    app.music_sl.track = {panel_x + 120, 70, pw - 200, 20};
    app.sfx_sl.track = {panel_x + 120, 122, pw - 200, 20};
    app.lp_x = 14.f + tile + 20.f;
    app.lp_w = std::min(196.f, Wd * 0.235f);
    app.rp_w = std::min(204.f, Wd * 0.25f);
    app.rp_x = Wd - 18.f - app.rp_w;
    app.play_rect = {app.rp_x, Hd - 76.f, app.rp_w, 58.f};
    app.mode_l = {app.lp_x, 158.f, 44.f, 66.f};
    app.mode_r = {app.lp_x + app.lp_w - 44.f, 158.f, 44.f, 66.f};
    app.logout_rect = {panel_x + 4.f, 190.f, 180.f, 40.f};
}

static float ease_out(float t) {
    t = t < 0 ? 0 : (t > 1 ? 1 : t);
    return 1 - (1 - t) * (1 - t) * (1 - t);
}

static void send_pref(const char* k, const std::string& v);

static void play_click();

static void save_volumes() {
    send_pref("music_volume", std::to_string(int(app.music_vol * 100.f + 0.5f)));
    send_pref("sfx_volume", std::to_string(int(app.sfx_vol * 100.f + 0.5f)));
}

static void draw_telegram_icon(float x, float y, float s, float cr, float cg, float cb, float ca) {
    float p[7][2] = {
        {0.08f, 0.45f}, {0.92f, 0.12f}, {0.62f, 0.86f}, {0.46f, 0.62f},
        {0.30f, 0.76f}, {0.34f, 0.56f}, {0.72f, 0.26f}};
    struct T { int a, b, c; } tris[4] = {{0, 1, 2}, {0, 2, 3}, {3, 2, 4}, {5, 6, 3}};
    for (auto& t : tris) {
        float vx[3], vy[3];
        int ids[3] = {t.a, t.b, t.c};
        for (int k = 0; k < 3; k++) {
            vx[k] = x + p[ids[k]][0] * s;
            vy[k] = y + p[ids[k]][1] * s;
        }
        for (int k = 1; k < 2; k++) {}
        float minx = std::min(vx[0], std::min(vx[1], vx[2]));
        float maxx = std::max(vx[0], std::max(vx[1], vx[2]));
        float miny = std::min(vy[0], std::min(vy[1], vy[2]));
        float maxy = std::max(vy[0], std::max(vy[1], vy[2]));
        for (float py = floor(miny); py <= maxy; py += 1.f) {
            for (float px2 = floor(minx); px2 <= maxx; px2 += 1.f) {
                float sx = px2 + 0.5f, sy = py + 0.5f;
                float d0 = (vx[1] - vx[0]) * (sy - vy[0]) - (vy[1] - vy[0]) * (sx - vx[0]);
                float d1 = (vx[2] - vx[1]) * (sy - vy[1]) - (vy[2] - vy[1]) * (sx - vx[1]);
                float d2 = (vx[0] - vx[2]) * (sy - vy[2]) - (vy[0] - vy[2]) * (sx - vx[2]);
                bool neg = (d0 < 0) || (d1 < 0) || (d2 < 0);
                bool pos = (d0 > 0) || (d1 > 0) || (d2 > 0);
                if (!(neg && pos)) {
                    push_shape(px2, py, 1.f, 1.f, 0.f, cr, cg, cb, ca, 0, 0, 0, 0);
                }
            }
        }
    }
}

static int system_language() {
#ifdef __ANDROID__
    char buf[PROP_VALUE_MAX]{};
    __system_property_get("persist.sys.locale", buf);
    std::string locale(buf);
    if (locale.empty()) {
        __system_property_get("ro.product.locale", buf);
        locale = buf;
    }
    std::string low = security::lower_copy(locale);
    if (low.rfind("ru", 0) == 0 || low.find("-ru") != std::string::npos || low.find("_ru") != std::string::npos) return 0;
    if (low.rfind("tr", 0) == 0 || low.find("-tr") != std::string::npos || low.find("_tr") != std::string::npos) return 2;
#endif
    return 1;
}

static void text_glow(float x, float y, const std::string& s, float size, float ls, Col c, Col g, float ga, bool title);
static void hline(float x0, float x1, float y, float th, Col a, Col b);
static void card(float x, float y, float w, float h, float cham, float a, bool accent, int ty);

static std::vector<std::string> wrap_security_text(const std::string& s, float size, float spacing, float max_width) {
    std::vector<std::string> lines;
    std::string current;
    std::string word;

    auto flush_word = [&]() {
        if (word.empty()) return;
        std::string candidate = current.empty() ? word : current + " " + word;
        if (!current.empty() && tr.measure(candidate, size, spacing) > max_width) {
            lines.push_back(current);
            current = word;
        } else {
            current = candidate;
        }
        word.clear();
    };

    for (size_t i = 0; i <= s.size(); ++i) {
        if (i == s.size() || s[i] == ' ' || s[i] == '\n') {
            flush_word();
            if (i < s.size() && s[i] == '\n' && !current.empty()) {
                lines.push_back(current);
                current.clear();
            }
        } else {
            word += s[i];
        }
    }

    if (!current.empty()) lines.push_back(current);
    return lines;
}

static void draw_security_screen() {
    const int ev = security::event();
    if (ev == security::EVENT_NONE) return;

    const float W = float(app.vw) / app.dp;
    const float H = float(app.vh) / app.dp;

    if (glr::gl_ctx.ls_tex) {
        push_tex_quad(nullptr, 10, 0.f, 0.f, W, H, 1.f, 1.f, 1.f, 1.f);
    } else {
        push_shape(0.f, 0.f, W, H, 0.f, 0.018f, 0.016f, 0.022f, 1.f, 0.f, 0.f, 0.f, 0.f);
    }

    push_shape(0.f, 0.f, W, H, 0.f, 0.008f, 0.008f, 0.01f, 0.68f, 0.f, 0.f, 0.f, 0.f);

    int lang = app.lang;
    if (lang < 0 || lang > 2) lang = system_language();
    const SecurityStrings& ss = SECURITY_STRINGS[lang];
    const char* body = ev == security::EVENT_ROOT ? ss.root :
                       ev == security::EVENT_WINDOWS_EMULATOR ? ss.emulator : ss.tamper;

    const float pw = std::min(W - 44.f, 560.f);
    const float size = W < 430.f ? 13.2f : 15.f;
    const float spacing = W < 430.f ? 0.55f : 0.7f;
    const float max_text_w = pw - 44.f;
    std::vector<std::string> body_lines = wrap_security_text(body, size, spacing, max_text_w);

    const float body_line_h = size * 1.72f;
    const float ph = std::min(
        std::max(48.f + float(body_lines.size()) * body_line_h + 26.f, 184.f),
        H - 48.f
    );

    const float cx = W * 0.5f;
    const float cy = H * 0.5f;
    const float x = cx - pw * 0.5f;
    const float y = cy - ph * 0.5f;

    push_fx(9, cx, cy, pw * 0.52f, ph * 0.52f, 0.f, 28.f, 18.f, 2,
            cmk(0.86f, 0.18f, 0.12f, 0.18f), K_NONE, K_NONE);
    card(x, y, pw, ph, 18.f, 1.f, true, 2);

    push_shape(x + 20.f, y + 54.f, pw - 40.f, 1.f, 0.f,
               0.86f, 0.2f, 0.14f, 0.55f, 0.f, 0.f, 0.f, 0.f);

    const float title_size = W < 430.f ? 23.f : 27.f;
    const float tw = tr.measure("ERROR", title_size, 1.4f, true);
    text_glow(cx - tw * 0.5f, y + 38.f, "ERROR", title_size, 1.4f,
              cmk(1.f, 0.92f, 0.9f, 1.f), cmk(0.96f, 0.15f, 0.1f, 1.f), 0.24f, true);

    const float start_y = y + 82.f;
    for (size_t i = 0; i < body_lines.size(); ++i) {
        const float bw = tr.measure(body_lines[i], size, spacing);
        tr.draw_text(cx - bw * 0.5f, start_y + float(i) * body_line_h,
                     body_lines[i], size, spacing, 0.94f, 0.93f, 0.92f, 0.98f);
    }

    const float pulse = 0.55f + 0.25f * sinf(app.time * 2.4f);
    hline(x + 20.f, x + pw - 20.f, y + ph - 20.f, 1.f,
          cmk(0.96f, 0.76f, 0.2f, pulse), cmk(0.96f, 0.76f, 0.2f, 0.f));
}

static void draw_loading() {
    const float dp = 1.f;
    float W = app.vw / app.dp, H = app.vh / app.dp;
    push_tex_quad(nullptr, 10, 0, 0, float(W), float(H), 1, 1, 1, ease_out(app.fade_in));
    if (app.fade_in >= 0.55f && glr::gl_ctx.ls_tex) {
        float Wd = float(W), Hd = float(H);
        float img_asp = 1672.f / 941.f;
        float scr_asp = Wd / Hd;
        float bw, bh;
        if (scr_asp > img_asp) {
            bw = Wd;
            bh = Wd / img_asp;
        } else {
            bh = Hd;
            bw = Hd * img_asp;
        }
        float bar_w = std::min(340.f * dp, bw * 0.46f);
        float bar_h = 7.f * dp;
        float bar_x = (Wd - bar_w) * 0.5f;
        float bar_y = Hd * 0.685f - bar_h * 0.5f;
        push_shape(bar_x - 2.f * dp, bar_y - 2.f * dp, bar_w + 4.f * dp, bar_h + 4.f * dp, bar_h, 0, 0, 0, 0.5f * ease_out(app.fade_in), 1.f, 0.78f, 0.28f, 0.55f * ease_out(app.fade_in));
        push_shape(bar_x, bar_y, bar_w, bar_h, bar_h, 0.043f, 0.039f, 0.047f, 0.78f * ease_out(app.fade_in), 1.f, 0.78f, 0.28f, 0.18f * ease_out(app.fade_in));
        float fill = app.shown_progress / 100.f;
        if (fill > 0.003f) {
            float fw = std::max(bar_w * fill, bar_h);
            push_shape(bar_x, bar_y, fw, bar_h, bar_h, 0.96f, 0.76f, 0.2f, ease_out(app.fade_in), 0, 0, 0, 0);
            float glow = 0.25f + 0.15f * sinf(app.time * 4.f);
            push_shape(bar_x - 1.f * dp, bar_y - 1.f * dp, fw + 2.f * dp, bar_h + 2.f * dp, bar_h, 0, 0, 0, 0, 1.f, 0.8f, 0.3f, glow * ease_out(app.fade_in));
        }
        char pct[16];
        snprintf(pct, sizeof(pct), "%d%%", int(app.shown_progress + 0.5f));
        std::string lt = STRINGS[app.lang].loading + std::string(pct);
        float ts = 15.f;
        float tw = tr.measure(lt, ts, 1.2f);
        tr.draw_text((Wd - tw) * 0.5f, bar_y + bar_h + 30.f * dp, lt, ts, 1.2f, 0.92f, 0.9f, 0.88f, 0.92f * ease_out(app.fade_in));
    }
}

static float hf(float n) {
    float s = sinf(n * 127.1f) * 43758.5453f;
    return s - floorf(s);
}

static float clamp01(float v) { return v < 0.f ? 0.f : (v > 1.f ? 1.f : v); }

static float sstep(float a, float b, float x) {
    float t = clamp01((x - a) / (b - a));
    return t * t * (3.f - 2.f * t);
}

static void text_center(float cx, float y, const std::string& s, float size, float ls, Col c, bool title) {
    float w = tr.measure(s, size, ls, title);
    tr.draw_text(cx - w * 0.5f, y, s, size, ls, c.r, c.g, c.b, c.a, title);
}

static void text_right(float rx, float y, const std::string& s, float size, float ls, Col c, bool title) {
    float w = tr.measure(s, size, ls, title);
    tr.draw_text(rx - w, y, s, size, ls, c.r, c.g, c.b, c.a, title);
}

static void text_glow(float x, float y, const std::string& s, float size, float ls, Col c, Col g, float ga, bool title) {
    const float o1[4][2] = {{-1.5f, 0.f}, {1.5f, 0.f}, {0.f, -1.5f}, {0.f, 1.5f}};
    const float o2[4][2] = {{-2.6f, -2.6f}, {2.6f, -2.6f}, {-2.6f, 2.6f}, {2.6f, 2.6f}};
    for (auto& d : o2) tr.draw_text(x + d[0], y + d[1], s, size, ls, g.r, g.g, g.b, ga * 0.5f * c.a, title);
    for (auto& d : o1) tr.draw_text(x + d[0], y + d[1], s, size, ls, g.r, g.g, g.b, ga * c.a, title);
    tr.draw_text(x, y, s, size, ls, c.r, c.g, c.b, c.a, title);
}

static void bracket(float x, float y, float sx, float sy, float len, float th, Col c) {
    float hx = sx > 0.f ? x : x - len;
    float hy = sy > 0.f ? y : y - th;
    push_shape(hx, hy, len, th, 0.f, c.r, c.g, c.b, c.a, 0, 0, 0, 0);
    float vx = sx > 0.f ? x : x - th;
    float vy = sy > 0.f ? y : y - len;
    push_shape(vx, vy, th, len, 0.f, c.r, c.g, c.b, c.a, 0, 0, 0, 0);
}

static void hline(float x0, float x1, float y, float th, Col a, Col b) {
    push_fx(0, (x0 + x1) * 0.5f, y, (x1 - x0) * 0.5f, th * 0.5f, 0.f, 0.f, 0.f, 1, a, b, K_NONE);
}

static void diamond(float cx, float cy, float s, Col c) {
    push_fx(4, cx, cy, s, s, 0.f, s, 0.f, 0, c, c, K_NONE);
}

static void card(float x, float y, float w, float h, float cham, float a, bool accent, int ty = 2) {
    float hw = w * 0.5f, hh = h * 0.5f, cx = x + hw, cy = y + hh;
    if (accent) push_fx(1, cx, cy, hw, hh, 24.f, 0.f, 10.f, 2, cmk(0.96f, 0.76f, 0.2f, 0.12f * a), K_NONE, K_NONE);
    push_fx(ty, cx, cy, hw, hh, 0.f, cham, 1.f, 0, cmk(0.11f, 0.10f, 0.12f, 0.80f * a), cmk(0.04f, 0.035f, 0.045f, 0.88f * a),
            cmk(1.f, 1.f, 1.f, 0.15f * a), 0.f, 0.f, 0.f, 0.06f);
    Col rc = cmk(0.96f, 0.76f, 0.2f, 0.95f * a);
    if (ty == 2) {
        push_fx(0, x + 1.25f, cy + cham * 0.5f, 1.25f, hh - cham * 0.5f, 0.f, 0.f, 0.f, 0,
                cmk(1.f, 0.86f, 0.38f, 0.95f * a), cmk(0.6f, 0.42f, 0.06f, 0.95f * a), K_NONE);
        bracket(x + w, y, -1.f, 1.f, 9.f, 1.5f, rc);
        bracket(x, y + h, 1.f, -1.f, 9.f, 1.5f, rc);
    } else {
        push_fx(0, x + w - 1.25f, cy - cham * 0.5f, 1.25f, hh - cham * 0.5f, 0.f, 0.f, 0.f, 0,
                cmk(1.f, 0.86f, 0.38f, 0.95f * a), cmk(0.6f, 0.42f, 0.06f, 0.95f * a), K_NONE);
        bracket(x, y, 1.f, 1.f, 9.f, 1.5f, rc);
        bracket(x + w, y + h, -1.f, -1.f, 9.f, 1.5f, rc);
    }
}

static void draw_particles(float Wd, float Hd, float k) {
    float t = app.time;
    for (int i = 0; i < 64; i++) {
        float fi = float(i);
        float h1 = hf(fi + 1.f), h2 = hf(fi * 3.1f + 7.f), h3 = hf(fi * 5.7f + 2.f), h4 = hf(fi * 9.3f + 4.f);
        float speed = 10.f + h2 * 28.f;
        float cycle = Hd + 24.f;
        float yy = Hd + 12.f - fmodf(t * speed + h3 * cycle, cycle);
        float xx = h1 * Wd + sinf(t * (0.4f + h4) + fi) * (6.f + 10.f * h2);
        float life = yy / Hd;
        float al = sstep(1.05f, 0.9f, life) * sstep(0.f, 0.2f, life);
        float tw = 0.6f + 0.4f * sinf(t * (2.f + h4 * 4.f) + fi * 2.f);
        float sz = 0.7f + h4 * 1.5f;
        Col c = cmk(1.f, 0.62f + 0.25f * h3, 0.14f, (0.35f + 0.5f * h2) * al * tw * k);
        push_fx(1, xx, yy, sz * 0.5f, sz * 0.5f, sz * 3.8f, sz * 0.5f, sz * 1.6f, 2, c, K_NONE, K_NONE);
    }
    for (int i = 0; i < 8; i++) {
        float fi = float(i) + 40.f;
        float h1 = hf(fi + 1.f), h2 = hf(fi * 2.3f), h3 = hf(fi * 4.1f);
        float r = 9.f + 22.f * h2;
        float x = fmodf(h1 * Wd + t * (1.5f + 3.f * h3), Wd + 2.f * r) - r;
        float y = h3 * Hd + sinf(t * 0.2f + fi) * 10.f;
        float al = (0.05f + 0.04f * sinf(t * 0.6f + fi * 3.f)) * k;
        push_fx(8, x, y, r, r, 0.f, 0.f, 1.f, 2, cmk(1.f, 0.82f, 0.34f, al * 0.6f), K_NONE, cmk(1.f, 0.84f, 0.38f, al * 2.f));
    }
}

static void draw_platform(float Wd, float Hd, float k) {
    if (k < 0.01f) return;
    float t = app.time;
    float cx = Wd * 0.5f, fy = Hd * 0.86f;
    push_fx(9, cx, fy, 110.f, 12.f, 46.f, 0.f, 20.f, 2, cmk(0.97f, 0.74f, 0.18f, 0.55f * k), K_NONE, K_NONE);
    for (int i = 0; i < 2; i++) {
        float ph = fmodf(t * 0.45f + float(i) * 0.5f, 1.f);
        float rx = 36.f + 120.f * ph;
        float a = (1.f - ph) * (1.f - ph) * 0.8f * k;
        push_fx(8, cx, fy, rx, rx * 0.16f, 0.f, 0.f, 1.4f, 2, K_NONE, K_NONE, cmk(1.f, 0.82f, 0.32f, a));
    }
    push_fx(8, cx, fy, 74.f, 11.8f, 0.f, 0.f, 1.f, 2, cmk(0.92f, 0.7f, 0.14f, 0.06f * k), K_NONE, cmk(1.f, 0.84f, 0.38f, 0.5f * k));
    push_fx(8, cx, fy, 104.f, 16.6f, 0.f, 0.f, 0.8f, 2, K_NONE, K_NONE, cmk(1.f, 0.84f, 0.38f, 0.25f * k));
    for (int i = 0; i < 16; i++) {
        float a = t * 0.3f + float(i) * 0.3926991f;
        float px = cx + 74.f * cosf(a);
        float py = fy + 11.8f * sinf(a);
        float front = 0.35f + 0.65f * (0.5f + 0.5f * sinf(a));
        push_fx(0, px, py, 1.4f, 0.9f, 0.f, 0.f, 0.f, 2, cmk(1.f, 0.88f, 0.5f, 0.8f * front * k), K_NONE, K_NONE);
    }
}

static void draw_hud(float Wd, float Hd) {
    float t = app.time;
    float a = ease_out(std::min(1.f, app.intro / 0.8f));
    Col rc = cmk(0.96f, 0.76f, 0.2f, 0.9f * a);
    Col wc = cmk(1.f, 1.f, 1.f, 0.30f * a);
    float cs[4][4] = {{7.f, 7.f, 1.f, 1.f}, {Wd - 7.f, 7.f, -1.f, 1.f}, {7.f, Hd - 7.f, 1.f, -1.f}, {Wd - 7.f, Hd - 7.f, -1.f, -1.f}};
    for (auto& c : cs) {
        bracket(c[0], c[1], c[2], c[3], 26.f, 1.6f, rc);
        bracket(c[0] + c[2] * 6.f, c[1] + c[3] * 6.f, c[2], c[3], 10.f, 1.f, wc);
    }
    hline(46.f, Wd - 46.f, 7.8f, 0.8f, cmk(1.f, 0.78f, 0.26f, 0.f), cmk(1.f, 0.78f, 0.26f, 0.10f * a));
    hline(46.f, Wd - 46.f, Hd - 7.8f, 0.8f, cmk(1.f, 0.78f, 0.26f, 0.10f * a), cmk(1.f, 0.78f, 0.26f, 0.f));
    float mx = 46.f + fmodf(t * 140.f, std::max(Wd - 92.f, 1.f));
    hline(mx - 22.f, mx, 7.8f, 1.2f, cmk(1.f, 0.9f, 0.58f, 0.f), cmk(1.f, 0.93f, 0.68f, 0.8f * a));
    float mx2 = Wd - mx;
    hline(mx2, mx2 + 22.f, Hd - 7.8f, 1.2f, cmk(1.f, 0.93f, 0.68f, 0.8f * a), cmk(1.f, 0.9f, 0.58f, 0.f));
    std::string vtxt = std::string("Version: ") + app.version;
    tr.draw_text(16.f, Hd - 14.f, vtxt, 9.f, 1.5f, 0.62f, 0.60f, 0.60f, 0.75f * a);
    text_right(Wd - 16.f, Hd - 14.f, "GRID 07-A", 9.f, 1.5f, cmk(0.62f, 0.60f, 0.60f, 0.75f * a), false);
}

static void draw_rail() {
    float t = app.time;
    Rect& r0 = app.tile_rects[0];
    Rect& r3 = app.tile_rects[3];
    float Hd = float(app.vh) / app.dp;
    float ra = ease_out(std::min(1.f, app.intro / 0.4f));
    push_fx(0, 42.f, Hd * 0.5f, 42.f, Hd * 0.5f, 0.f, 0.f, 0.f, 1, cmk(0.f, 0.f, 0.f, 0.55f * ra), cmk(0.f, 0.f, 0.f, 0.f), K_NONE);
    float lx = r0.x + r0.w * 0.5f;
    push_fx(0, lx, (r0.y + r3.y + r3.h) * 0.5f, 0.6f, (r3.y + r3.h - r0.y) * 0.5f + 18.f, 0.f, 0.f, 0.f, 0,
            cmk(0.96f, 0.76f, 0.2f, 0.f), cmk(0.96f, 0.76f, 0.2f, 0.45f * ra), K_NONE);
    for (int i = 0; i < 4; i++) {
        Rect& r = app.tile_rects[i];
        bool active = app.page == i;
        float ee = ease_out(clamp01((app.intro - 0.08f * float(i)) / 0.45f));
        float off = (1.f - ee) * -30.f;
        float press = (app.press_tile == i) ? (1.f - 0.06f * ease_out(app.press_tile_t)) : 1.f;
        float cx = r.x + r.w * 0.5f + off;
        float cy = r.y + r.h * 0.5f;
        float w = r.w * press, h = r.h * press;
        if (active) {
            push_fx(1, cx, cy, w * 0.5f, h * 0.5f, 26.f, 0.f, 11.f, 2,
                    cmk(0.96f, 0.76f, 0.2f, (0.5f + 0.15f * sinf(t * 3.f)) * ee), K_NONE, K_NONE);
        }
        if (active) {
            push_fx(2, cx, cy, w * 0.5f, h * 0.5f, 0.f, 11.f, 1.f, 0, cmk(1.f, 0.82f, 0.32f, 0.97f * ee), cmk(0.62f, 0.44f, 0.07f, 0.97f * ee),
                    cmk(1.f, 0.93f, 0.72f, 0.75f * ee), fmodf(t * 0.5f, 1.7f) - 0.35f, 0.10f, 0.f, 0.f);
        } else {
            push_fx(2, cx, cy, w * 0.5f, h * 0.5f, 0.f, 11.f, 1.f, 0, cmk(0.13f, 0.12f, 0.14f, 0.80f * ee), cmk(0.06f, 0.055f, 0.065f, 0.82f * ee),
                    cmk(1.f, 1.f, 1.f, 0.14f * ee), 0.f, 0.f, 0.f, 0.06f);
        }
        if (active) {
            push_fx(0, r.x + off - 5.f, cy, 1.5f, h * 0.5f - 8.f, 0.f, 1.5f, 0.f, 0, cmk(1.f, 0.86f, 0.38f, ee), cmk(0.7f, 0.5f, 0.08f, ee), K_NONE);
        }
        if (glr::gl_ctx.btn_tex[i]) {
            float isz = 34.f * press;
            float k = active ? 1.f : 0.72f;
            push_tex_quad(nullptr, 20 + i, cx - isz * 0.5f, cy - isz * 0.5f, isz, isz,
                          active ? 1.f : 0.86f, active ? 0.97f : 0.84f, active ? 0.95f : 0.82f, k * ee, 3);
        }
        char num[4];
        snprintf(num, sizeof(num), "0%d", i + 1);
        tr.draw_text(cx + w * 0.5f - 15.f, cy + h * 0.5f - 5.f, num, 7.5f, 0.8f, active ? 1.f : 0.6f, active ? 0.9f : 0.58f, active ? 0.85f : 0.58f, 0.8f * ee);
    }
}

static void draw_home() {
    float Wd = float(app.vw) / app.dp, Hd = float(app.vh) / app.dp;
    float t = app.time;
    float anim = ease_out(app.page_anim);
    const Strings& S = STRINGS[app.lang];
    auto ent = [&](float d) { return ease_out(clamp01((app.intro - d) / 0.55f)) * anim; };

    float ts = 28.f;
    float tw = tr.measure("WARARENA", ts, 7.f, true);
    float tx = (Wd - tw) * 0.5f;
    float ty = 24.f + ts;
    float ti = ent(0.f);
    push_fx(9, Wd * 0.5f, ty - 10.f, tw * 0.5f + 20.f, 12.f, 60.f, 0.f, 26.f, 2, cmk(0.96f, 0.76f, 0.2f, 0.32f * ti * (0.8f + 0.2f * sinf(t * 2.f))), K_NONE, K_NONE);
    if (fmodf(t, 6.1f) < 0.12f) {
        tr.draw_text(tx - 3.f, ty, "WARARENA", ts, 7.f, 1.f, 0.78f, 0.15f, 0.55f * ti, true);
        tr.draw_text(tx + 3.f, ty, "WARARENA", ts, 7.f, 0.1f, 0.8f, 1.f, 0.45f * ti, true);
    }
    text_glow(tx, ty, "WARARENA", ts, 7.f, cfade(K_WHITE, ti * 0.97f), K_GOLD, 0.16f, true);
    float ly = ty - 10.f;
    float lw = 120.f * ti;
    hline(tx - 18.f - lw, tx - 18.f, ly, 2.f, cmk(0.96f, 0.76f, 0.2f, 0.f), cmk(0.96f, 0.76f, 0.2f, 0.95f * ti));
    hline(tx + tw + 18.f, tx + tw + 18.f + lw, ly, 2.f, cmk(0.96f, 0.76f, 0.2f, 0.95f * ti), cmk(0.96f, 0.76f, 0.2f, 0.f));
    hline(tx - 18.f - lw * 0.6f, tx - 18.f, ly + 6.f, 1.f, cmk(1.f, 1.f, 1.f, 0.f), cmk(1.f, 1.f, 1.f, 0.22f * ti));
    hline(tx + tw + 18.f, tx + tw + 18.f + lw * 0.6f, ly + 6.f, 1.f, cmk(1.f, 1.f, 1.f, 0.22f * ti), cmk(1.f, 1.f, 1.f, 0.f));
    diamond(tx - 18.f, ly, 3.5f, cmk(1.f, 0.84f, 0.38f, ti));
    diamond(tx + tw + 18.f, ly, 3.5f, cmk(1.f, 0.84f, 0.38f, ti));
    float uy = ty + 11.f;
    float uw = 130.f * ti;
    hline(Wd * 0.5f - uw * 0.5f, Wd * 0.5f, uy, 2.5f, cmk(0.96f, 0.76f, 0.2f, 0.f), cmk(0.96f, 0.76f, 0.2f, 0.95f));
    hline(Wd * 0.5f, Wd * 0.5f + uw * 0.5f, uy, 2.5f, cmk(0.96f, 0.76f, 0.2f, 0.95f), cmk(0.96f, 0.76f, 0.2f, 0.f));
    float hx = Wd * 0.5f + sinf(t * 1.6f) * uw * 0.45f;
    push_fx(1, hx, uy, 6.f, 1.f, 12.f, 1.f, 6.f, 2, cmk(1.f, 0.93f, 0.68f, 0.8f * ti), K_NONE, K_NONE);

    float lx = app.lp_x, lpw = app.lp_w;
    float ea = ent(0.10f);
    float xa = lx - (1.f - ea) * 40.f;
    float ya = 62.f, ha = 86.f;
    card(xa, ya, lpw, ha, 14.f, ea, true);
    float as = 46.f, ax = xa + 12.f, ay = ya + 14.f;
    push_fx(4, ax + as * 0.5f, ay + as * 0.5f, as * 0.5f, as * 0.5f, 0.f, 9.f, 1.2f, 0, cmk(0.2f, 0.15f, 0.06f, 0.95f * ea),
            cmk(0.06f, 0.05f, 0.03f, 0.95f * ea), cmk(0.96f, 0.76f, 0.2f, 0.95f * ea));
    push_fx(8, ax + as * 0.5f, ay + as * 0.36f, 7.f, 8.5f, 0.f, 0.f, 0.f, 0, cmk(0.88f, 0.86f, 0.85f, 0.9f * ea), cmk(0.55f, 0.53f, 0.52f, 0.9f * ea), K_NONE);
    push_fx(0, ax + as * 0.5f, ay + as * 0.80f, 14.f, 7.f, 0.f, 7.f, 0.f, 0, cmk(0.75f, 0.73f, 0.72f, 0.9f * ea), cmk(0.45f, 0.43f, 0.42f, 0.9f * ea), K_NONE);
    tr.draw_text(xa + 68.f, ya + 25.f, S.operative, 9.5f, 2.2f, 0.62f, 0.60f, 0.60f, ea);
    push_fx(2, xa + 68.f + 22.f, ya + 57.f, 22.f, 7.f, 0.f, 4.f, 1.f, 0, cmk(0.96f, 0.76f, 0.2f, 0.22f * ea), cmk(0.96f, 0.76f, 0.2f, 0.10f * ea), cmk(0.96f, 0.76f, 0.2f, 0.8f * ea));
    text_center(xa + 68.f + 22.f, ya + 60.f, "LVL 01", 8.5f, 1.f, cmk(1.f, 0.95f, 0.75f, ea), false);
    float bx = xa + 12.f, by = ya + ha - 13.f, bwid = lpw - 24.f;
    push_fx(0, bx + bwid * 0.5f, by, bwid * 0.5f, 2.f, 0.f, 1.f, 0.8f, 0, cmk(0.05f, 0.05f, 0.06f, 0.9f * ea), cmk(0.05f, 0.05f, 0.06f, 0.9f * ea), cmk(1.f, 1.f, 1.f, 0.18f * ea));
    float fw = bwid * 0.18f;
    push_fx(0, bx + fw * 0.5f, by, fw * 0.5f, 2.f, 0.f, 1.f, 0.f, 1, cmk(0.6f, 0.42f, 0.06f, ea), cmk(1.f, 0.84f, 0.34f, ea), K_NONE, fmodf(t * 0.6f, 1.6f) - 0.3f, 0.15f, 0.f, 0.f);

    float eb = ent(0.18f);
    float xb = lx - (1.f - eb) * 40.f;
    float yb = 158.f, hb = 66.f;
    card(xb, yb, lpw, hb, 12.f, eb, false);
    tr.draw_text(xb + 14.f, yb + 19.f, S.mode_lbl, 9.f, 2.2f, 0.62f, 0.60f, 0.60f, eb);
    float slide = (1.f - ease_out(app.mode_anim)) * 18.f * float(app.mode_dir);
    float ma = ease_out(app.mode_anim) * eb;
    float msize = 14.f;
    float mw = tr.measure(S.modes[app.mode], msize, 1.6f, true);
    float mavail = lpw - 84.f;
    if (mw > mavail) msize *= mavail / mw;
    text_center(xb + lpw * 0.5f + slide, yb + 44.f, S.modes[app.mode], msize, 1.6f, cmk(0.95f, 0.93f, 0.91f, ma), true);
    float la = app.press_btn == 1 ? 1.f : 0.65f;
    float raa = app.press_btn == 2 ? 1.f : 0.65f;
    float nudge = 2.f * sinf(t * 4.f);
    tr.draw_text(xb + 15.f - nudge, yb + 46.f, "<", 20.f, 0.f, 0.96f, 0.76f, 0.2f, la * eb, true);
    tr.draw_text(xb + lpw - 26.f + nudge, yb + 46.f, ">", 20.f, 0.f, 0.96f, 0.76f, 0.2f, raa * eb, true);
    for (int i = 0; i < 3; i++) {
        bool on = i == app.mode;
        push_shape(xb + lpw * 0.5f - 16.f + float(i) * 11.f, yb + hb - 13.f, on ? 8.f : 5.f, 2.f, 1.f, on ? 0.96f : 0.6f, on ? 0.76f : 0.58f, on ? 0.20f : 0.58f, (on ? 1.f : 0.6f) * eb, 0, 0, 0, 0);
    }

    float rx = app.rp_x, rpw = app.rp_w;
    float ed = ent(0.14f);
    float xd = rx + (1.f - ed) * 40.f;
    float yd = 62.f, hd = 86.f;
    card(xd, yd, rpw, hd, 14.f, ed, true, 3);
    push_fx(0, xd + rpw * 0.5f, yd + 9.f, (rpw - 36.f) * 0.5f, 2.5f, 0.f, 0.f, 0.f, 0, cmk(0.32f, 0.22f, 0.03f, 0.9f * ed), cmk(0.32f, 0.22f, 0.03f, 0.9f * ed), K_NONE, 0.f, 0.f, 1.6f, 0.f);
    tr.draw_text(xd + 16.f, yd + 29.f, S.season, 9.f, 3.f, 0.62f, 0.60f, 0.60f, ed);
    text_glow(xd + 14.f, yd + 66.f, "01", 38.f, 3.f, cfade(K_WHITE, ed), K_GOLD, 0.18f, true);
    float ox = xd + rpw - 44.f, oy = yd + hd * 0.5f + 4.f;
    push_fx(8, ox, oy, 21.f, 21.f, 0.f, 0.f, 1.2f, 2, cmk(0.96f, 0.76f, 0.2f, 0.06f * ed), K_NONE, cmk(1.f, 0.82f, 0.34f, 0.85f * ed));
    push_fx(8, ox, oy, 13.f, 13.f, 0.f, 0.f, 0.7f, 2, K_NONE, K_NONE, cmk(1.f, 1.f, 1.f, 0.35f * ed));
    push_fx(8, ox, oy, 3.f, 3.f, 0.f, 0.f, 0.f, 0, cmk(1.f, 0.84f, 0.38f, ed), cmk(1.f, 0.84f, 0.38f, ed), K_NONE);
    for (int i = 0; i < 8; i++) {
        float a = t * 0.8f + float(i) * 0.7853982f;
        float al = 0.35f + 0.65f * (0.5f + 0.5f * sinf(a * 2.f));
        push_fx(0, ox + 27.f * cosf(a), oy + 27.f * sinf(a), 1.3f, 1.3f, 0.f, 0.f, 0.f, 2, cmk(1.f, 0.88f, 0.5f, al * ed), K_NONE, K_NONE);
    }

    float ep = ent(0.30f);
    Rect& pr = app.play_rect;
    float press = app.press_btn == 0 ? (1.f - 0.05f * ease_out(app.press_btn_t)) : 1.f;
    float pw = pr.w * press, ph = pr.h * press;
    float pcx = pr.x + pr.w * 0.5f + (1.f - ep) * 40.f, pcy = pr.y + pr.h * 0.5f;
    float gp = 0.34f + 0.18f * sinf(t * 3.f);
    push_fx(1, pcx, pcy, pw * 0.5f, ph * 0.5f, 32.f, 0.f, 14.f, 2, cmk(1.f, 0.78f, 0.25f, gp * ep), K_NONE, K_NONE);
    push_fx(3, pcx, pcy, pw * 0.5f, ph * 0.5f, 0.f, 14.f, 1.2f, 0, cmk(1.f, 0.82f, 0.32f, ep), cmk(0.58f, 0.4f, 0.05f, ep),
            cmk(1.f, 0.9f, 0.66f, 0.8f * ep), fmodf(t * 0.5f, 1.7f) - 0.35f, 0.12f, 0.10f, 0.f);
    hline(pcx - pw * 0.5f + 18.f, pcx + pw * 0.5f - 18.f, pcy - ph * 0.5f + 3.f, 1.f, cmk(1.f, 1.f, 1.f, 0.f), cmk(1.f, 1.f, 1.f, 0.40f * ep));
    float pls = 26.f;
    float plw = tr.measure(S.play, pls, 6.f, true);
    float total = plw + 14.f + 27.f;
    float px0 = pcx - total * 0.5f;
    tr.draw_text(px0 + 1.5f, pcy + pls * 0.36f + 1.5f, S.play, pls, 6.f, 0.f, 0.f, 0.f, 0.45f * ep, true);
    tr.draw_text(px0, pcy + pls * 0.36f, S.play, pls, 6.f, 1.f, 0.97f, 0.95f, ep, true);
    for (int i = 0; i < 3; i++) {
        float al = 0.25f + 0.75f * std::max(0.f, sinf(t * 5.f - float(i) * 0.9f));
        tr.draw_text(px0 + plw + 14.f + float(i) * 9.f, pcy + 20.f * 0.36f, ">", 20.f, 0.f, 1.f, 0.97f, 0.95f, al * ep, true);
    }
    if (app.toast > 0.f) {
        float tq = clamp01(app.toast / 0.3f);
        float cw = tr.measure(S.soon, 10.f, 1.8f) + 28.f;
        float cy2 = pr.y - 22.f - (1.f - tq) * 6.f;
        push_fx(2, pcx, cy2, cw * 0.5f, 11.f, 0.f, 6.f, 1.f, 0, cmk(0.12f, 0.1f, 0.04f, 0.92f * tq), cmk(0.06f, 0.05f, 0.025f, 0.92f * tq), cmk(0.96f, 0.76f, 0.2f, 0.9f * tq));
        text_center(pcx, cy2 + 3.6f, S.soon, 10.f, 1.8f, cmk(1.f, 0.94f, 0.78f, tq), false);
    }

    float ph2 = fmodf(t, 5.f);
    float tipa = sstep(0.f, 0.4f, ph2) * sstep(5.f, 4.6f, ph2) * ent(0.4f);
    int ti2 = int(t / 5.f) % 3;
    std::string tip = std::string("// ") + S.tips[ti2];
    text_center(Wd * 0.5f, Hd - 24.f, tip, 10.f, 2.f, cmk(0.80f, 0.78f, 0.78f, 0.85f * tipa), false);
}

static void draw_center_msg(const char* msg, float size) {
    float Wd = float(app.vw) / app.dp, Hd = float(app.vh) / app.dp;
    float t = app.time;
    float anim = ease_out(app.page_anim);
    float tw = tr.measure(msg, size, 2.f, true);
    float pw = std::min(std::max(tw + 80.f, 300.f), Wd - 150.f);
    float ph = 150.f;
    float cx = Wd * 0.5f + (1.f - anim) * 30.f;
    float x = cx - pw * 0.5f, y = Hd * 0.5f - ph * 0.5f;
    card(x, y, pw, ph, 16.f, anim, true);
    int pg = app.page;
    float icy = y + 38.f;
    push_fx(9, cx, icy, 16.f, 16.f, 40.f, 0.f, 18.f, 2, cmk(0.96f, 0.76f, 0.2f, 0.4f * anim), K_NONE, K_NONE);
    float rp = fmodf(t * 0.6f, 1.f);
    push_fx(8, cx, icy, 22.f + 14.f * rp, 22.f + 14.f * rp, 0.f, 0.f, 1.f, 2, K_NONE, K_NONE, cmk(1.f, 0.82f, 0.34f, (1.f - rp) * 0.7f * anim));
    push_fx(8, cx, icy, 22.f, 22.f, 0.f, 0.f, 1.2f, 0, cmk(0.12f, 0.1f, 0.04f, 0.9f * anim), cmk(0.05f, 0.045f, 0.025f, 0.9f * anim), cmk(0.96f, 0.76f, 0.2f, 0.95f * anim));
    if (glr::gl_ctx.btn_tex[pg]) {
        push_tex_quad(nullptr, 20 + pg, cx - 15.f, icy - 15.f, 30.f, 30.f, 1.f, 0.92f, 0.9f, anim, 3);
    }
    text_glow(cx - tw * 0.5f, y + 86.f, msg, size, 2.f, cfade(K_WHITE, anim * 0.95f), K_GOLD, 0.14f, true);
    int n = 18;
    float bwid = 9.f, gap = 3.f;
    float total = float(n) * (bwid + gap) - gap;
    for (int i = 0; i < n; i++) {
        float ph3 = fmodf(t * 8.f - float(i), float(n));
        float lit = ph3 < 4.f ? 1.f - ph3 / 4.f : 0.f;
        push_shape(cx - total * 0.5f + float(i) * (bwid + gap), y + ph - 26.f, bwid, 4.f, 1.f, 0.96f, 0.76f, 0.2f, (0.15f + 0.85f * lit) * anim, 0, 0, 0, 0);
    }
}

static void draw_settings() {
    float Wd = float(app.vw) / app.dp, Hd = float(app.vh) / app.dp;
    float t = app.time;
    float panel_x = app.tab_rects[0].x;
    float anim = ease_out(app.page_anim);
    const Strings& S = STRINGS[app.lang];
    float px0 = panel_x - 12.f;
    card(px0, 10.f, Wd - px0 - 12.f, Hd - 20.f, 16.f, anim, true);
    hline(px0 + 14.f, Wd - 24.f, 62.f, 1.f, cmk(0.96f, 0.76f, 0.2f, 0.8f * anim), cmk(0.96f, 0.76f, 0.2f, 0.f));
    for (int i = 0; i < 3; i++) {
        Rect& r = app.tab_rects[i];
        bool active = app.tab == i;
        float press = (app.press_tab == i) ? (1.f - 0.05f * ease_out(app.press_tab_t)) : 1.f;
        const char* label = i == 0 ? S.tab_sound : (i == 1 ? S.tab_gfx : S.tab_misc);
        float cx = r.x + r.w * 0.5f, cy = r.y + r.h * 0.5f;
        float w = r.w * press, h = r.h * press;
        if (active) {
            push_fx(1, cx, cy, w * 0.5f, h * 0.5f, 20.f, 0.f, 9.f, 2, cmk(0.96f, 0.76f, 0.2f, 0.45f * anim), K_NONE, K_NONE);
            push_fx(2, cx, cy, w * 0.5f, h * 0.5f, 0.f, 8.f, 1.f, 0, cmk(1.f, 0.82f, 0.32f, 0.97f * anim), cmk(0.62f, 0.44f, 0.07f, 0.97f * anim),
                    cmk(1.f, 0.93f, 0.72f, 0.7f * anim), fmodf(t * 0.5f, 1.7f) - 0.35f, 0.10f, 0.f, 0.f);
        } else {
            push_fx(2, cx, cy, w * 0.5f, h * 0.5f, 0.f, 8.f, 1.f, 0, cmk(0.13f, 0.12f, 0.14f, 0.8f * anim), cmk(0.06f, 0.055f, 0.065f, 0.82f * anim),
                    cmk(1.f, 1.f, 1.f, 0.14f * anim));
        }
        float ts = 14.f;
        float tw = tr.measure(label, ts, 0.5f);
        tr.draw_text(cx - tw * 0.5f, cy + ts * 0.36f, label, ts, 0.5f, active ? 1.f : 0.82f, active ? 0.97f : 0.80f, active ? 0.95f : 0.79f, anim * (active ? 1.f : 0.85f));
    }
    if (app.tab == TAB_SOUND) {
        Slider* sls[2] = {&app.music_sl, &app.sfx_sl};
        const char* labels[2] = {S.music, S.sfx};
        for (int i = 0; i < 2; i++) {
            Slider& sl = *sls[i];
            Rect& tk = sl.track;
            float ts = 15.f;
            tr.draw_text(panel_x + 4.f, tk.y + tk.h * 0.5f + ts * 0.36f, labels[i], ts, 0.5f, 0.92f, 0.90f, 0.88f, anim);
            float ty = tk.y + tk.h * 0.5f;
            push_fx(0, tk.x + tk.w * 0.5f, ty, tk.w * 0.5f, 3.5f, 0.f, 2.f, 0.8f, 0, cmk(0.06f, 0.055f, 0.065f, 0.9f * anim), cmk(0.06f, 0.055f, 0.065f, 0.9f * anim), cmk(1.f, 1.f, 1.f, 0.16f * anim));
            float fw2 = std::max(tk.w * sl.value, 4.f);
            push_fx(1, tk.x + fw2 * 0.5f, ty, fw2 * 0.5f, 3.f, 12.f, 2.f, 7.f, 2, cmk(0.96f, 0.76f, 0.2f, 0.45f * anim), K_NONE, K_NONE);
            push_fx(0, tk.x + fw2 * 0.5f, ty, fw2 * 0.5f, 3.f, 0.f, 2.f, 0.f, 1, cmk(0.6f, 0.42f, 0.06f, anim), cmk(1.f, 0.84f, 0.34f, anim), K_NONE,
                    fmodf(t * 0.5f + float(i) * 0.3f, 1.6f) - 0.3f, 0.12f, 0.f, 0.f);
            for (int m = 0; m <= 10; m++) {
                float mx = tk.x + tk.w * float(m) / 10.f;
                bool major = m % 5 == 0;
                push_shape(mx - 0.5f, ty + 8.f, 1.f, major ? 5.f : 3.f, 0.f, 0.8f, 0.78f, 0.78f, (major ? 0.5f : 0.25f) * anim, 0, 0, 0, 0);
            }
            float thx = tk.x + tk.w * sl.value;
            push_fx(9, thx, ty, 8.f, 8.f, 24.f, 0.f, 10.f, 2, cmk(1.f, 0.78f, 0.26f, 0.6f * anim), K_NONE, K_NONE);
            push_fx(4, thx, ty, 9.f, 9.f, 0.f, 4.5f, 1.8f, 0, cmk(1.f, 0.97f, 0.95f, anim), cmk(0.78f, 0.76f, 0.75f, anim), cmk(0.96f, 0.76f, 0.2f, anim));
            char pct[8];
            snprintf(pct, sizeof(pct), "%d%%", int(sl.value * 100.f + 0.5f));
            push_fx(2, tk.x + tk.w + 34.f, ty, 20.f, 9.f, 0.f, 4.f, 0.8f, 0, cmk(0.12f, 0.1f, 0.04f, 0.8f * anim), cmk(0.06f, 0.05f, 0.025f, 0.8f * anim), cmk(0.96f, 0.76f, 0.2f, 0.7f * anim));
            text_center(tk.x + tk.w + 34.f, ty + 4.5f, pct, 12.f, 0.5f, cmk(0.95f, 0.93f, 0.91f, anim), false);
        }
    } else if (app.tab == TAB_GFX) {
        float ts = 15.f;
        std::string msg = S.gfx_msg;
        std::vector<std::string> lines;
        std::string cur;
        std::string word;
        for (size_t i = 0; i <= msg.size(); i++) {
            if (i == msg.size() || msg[i] == ' ') {
                if (!cur.empty() && tr.measure((cur + " " + word).c_str(), ts, 0.5f) > 340.f) {
                    lines.push_back(cur);
                    cur = word;
                } else {
                    if (!cur.empty()) cur += " ";
                    cur += word;
                }
                word.clear();
            } else word += msg[i];
        }
        if (!cur.empty()) lines.push_back(cur);
        float y0 = Hd * 0.42f - float(lines.size()) * ts * 0.9f;
        for (size_t i = 0; i < lines.size(); i++) {
            float tw = tr.measure(lines[i], ts, 0.5f);
            tr.draw_text(panel_x + 30.f + (340.f - tw) * 0.5f, y0 + float(i) * ts * 1.8f + ts, lines[i], ts, 0.5f, 0.92f, 0.9f, 0.88f, anim);
        }
        float ly = y0 + float(lines.size()) * ts * 1.8f + 8.f;
        for (int i = 0; i < 12; i++) {
            float ph3 = fmodf(t * 6.f - float(i), 12.f);
            float lit = ph3 < 4.f ? 1.f - ph3 / 4.f : 0.f;
            push_shape(panel_x + 30.f + 170.f - 90.f + float(i) * 15.f, ly, 12.f, 3.f, 1.f, 0.96f, 0.76f, 0.2f, (0.15f + 0.85f * lit) * anim, 0, 0, 0, 0);
        }
    } else {
        std::string vt = std::string(S.version) + ": " + app.version;
        float ts = 15.f;
        float rowy = 70.f;
        std::string lt2 = std::string(S.language) + ": " + S.lang_name;
        tr.draw_text(panel_x + 6.f, rowy + ts * 0.36f, lt2, ts, 0.5f, 0.92f, 0.90f, 0.88f, anim);
        Rect& cr2 = app.change_rect;
        float press = app.press_change ? (1.f - 0.06f * ease_out(app.press_change_t)) : 1.f;
        float ccx = cr2.x + cr2.w * 0.5f, ccy = cr2.y + cr2.h * 0.5f;
        push_fx(1, ccx, ccy, cr2.w * press * 0.5f, cr2.h * press * 0.5f, 18.f, 0.f, 8.f, 2, cmk(0.96f, 0.76f, 0.2f, 0.30f * anim), K_NONE, K_NONE);
        push_fx(2, ccx, ccy, cr2.w * press * 0.5f, cr2.h * press * 0.5f, 0.f, 8.f, 1.2f, 0, cmk(0.96f, 0.76f, 0.2f, 0.30f * anim), cmk(0.58f, 0.4f, 0.05f, 0.30f * anim),
                cmk(0.96f, 0.76f, 0.2f, anim), fmodf(t * 0.5f, 1.7f) - 0.35f, 0.10f, 0.f, 0.f);
        float btw = tr.measure(S.change, 13.f, 0.5f) * press;
        tr.draw_text(ccx - btw * 0.5f, ccy + 4.7f, S.change, 13.f, 0.5f, 0.97f, 0.95f, 0.93f, anim);
        float tgy = 128.f;
        float tpress = app.press_tg ? (1.f - 0.07f * ease_out(app.press_tg_t)) : 1.f;
        float tx = panel_x + 4.f + (40.f - 40.f * tpress) * 0.5f;
        push_fx(1, panel_x + 24.f, tgy + 20.f, 20.f * tpress, 20.f * tpress, 16.f, 0.f, 8.f, 2, cmk(0.2f, 0.62f, 0.87f, 0.35f * anim), K_NONE, K_NONE);
        push_shape(panel_x + 4.f - (1.f - tpress) * 2.f, tgy - (1.f - tpress) * 2.f, 40.f * tpress, 40.f * tpress, 12.f,
                   0.2f, 0.62f, 0.87f, anim, 0, 0, 0, 0);
        draw_telegram_icon(tx + 8.f, tgy + 8.f, 24.f * tpress, 1, 1, 1, anim);
        tr.draw_text(panel_x + 56.f, tgy + 20.f + ts * 0.36f, "Telegram", ts, 0.5f, 0.92f, 0.90f, 0.88f, anim);
        float vy = tgy + 58.f;
        hline(panel_x + 6.f, panel_x + 260.f, vy - 14.f, 1.f, cmk(0.96f, 0.76f, 0.2f, 0.6f * anim), cmk(0.96f, 0.76f, 0.2f, 0.f));
        tr.draw_text(panel_x + 6.f, vy + ts * 0.36f, vt, 14.f, 0.5f, 0.75f, 0.73f, 0.72f, anim);

        float lgy = tgy + 92.f;
        float lpress = app.press_logout ? (1.f - 0.06f * ease_out(app.press_logout_t)) : 1.f;
        Rect& lr = app.logout_rect;
        float lcx = lr.x + lr.w * 0.5f, lcy = lr.y + lr.h * 0.5f;
        push_fx(1, lcx, lcy, lr.w * lpress * 0.5f, lr.h * lpress * 0.5f, 18.f, 0.f, 8.f, 2,
                cmk(0.96f, 0.22f, 0.15f, 0.30f * anim), K_NONE, K_NONE);
        push_fx(2, lcx, lcy, lr.w * lpress * 0.5f, lr.h * lpress * 0.5f, 0.f, 8.f, 1.2f, 0,
                cmk(0.96f, 0.22f, 0.15f, 0.30f * anim), cmk(0.58f, 0.08f, 0.05f, 0.30f * anim),
                cmk(0.96f, 0.22f, 0.15f, anim), fmodf(t * 0.5f, 1.7f) - 0.35f, 0.10f, 0.f, 0.f);
        std::string lo = S.logout;
        float lotw = tr.measure(lo, 13.f, 0.5f) * lpress;
        tr.draw_text(lcx - lotw * 0.5f, lcy + 4.7f, lo, 13.f, 0.5f, 1.f, 0.94f, 0.92f, anim);
    }
}

static void draw_menu() {
    float W = app.vw / app.dp, H = app.vh / app.dp;
    float k = 0.35f + 0.65f * app.home_mix;
    push_shape(0, 0, float(W), float(H), 0, 0.043f, 0.035f, 0.043f, 0.08f + 0.84f * (1.f - app.home_mix), 0, 0, 0, 0);
    push_fx(6, W * 0.5f, H * 0.5f, W * 0.5f, H * 0.5f, 0.f, 0.f, 0.f, 0, K_NONE, K_NONE, K_NONE);
    draw_particles(W, H, k);
    draw_platform(W, H, app.home_mix);
    draw_rail();
    switch (app.page) {
        case PAGE_HOME: draw_home(); break;
        case PAGE_INV: draw_center_msg(STRINGS[app.lang].inv_msg, 19.f); break;
        case PAGE_CHAT: draw_center_msg(STRINGS[app.lang].chat_msg, 19.f); break;
        case PAGE_SET: draw_settings(); break;
    }
    draw_hud(W, H);
}


}

namespace pipeline {

static JavaVM* g_vm = nullptr;
static jobject g_activity = nullptr;
static jmethodID m_music_ready = nullptr;
static jmethodID m_click = nullptr;
static jmethodID m_tg = nullptr;
static jmethodID m_agent = nullptr;
static jmethodID m_agent_missing = nullptr;
static jmethodID m_music_vol = nullptr;
static jmethodID m_pref = nullptr;
static jmethodID m_set_pref = nullptr;
static jmethodID m_get_assets = nullptr;
static jmethodID m_show_auth = nullptr;
static jmethodID m_hide_auth = nullptr;
static jmethodID m_start_music = nullptr;
static jmethodID m_stop_music = nullptr;
static jmethodID m_logout = nullptr;
static jmethodID m_request_exit = nullptr;
static jmethodID m_session_get = nullptr;
static jmethodID m_session_clear_j = nullptr;
static jmethodID m_auth_image = nullptr;

static std::string g_cache_dir;
static std::string g_version;
static std::string g_music_path;
static AAssetManager* g_asset_mgr = nullptr;
static std::atomic<bool> g_loaded{false};
static std::atomic<float> g_progress{0.f};
static std::atomic<bool> g_agent_done{false};
static std::atomic<bool> g_quit{false};
static vaf::Archive g_archive;
static std::vector<u8> g_font_data;
static std::vector<u8> g_font_ru;
static std::vector<u8> g_font_tr;
static std::atomic<bool> g_font_ready{false};

static std::function<void()> g_show_auth_cb;
static std::function<void()> g_start_music_cb;
static std::function<void()> g_stop_music_cb;
static std::function<void()> g_logout_cb;
static std::function<void()> g_exit_cb;

struct AssetSource : vaf::VafSource {
    AAsset* a = nullptr;
    u64 sz = 0;
    bool open(const char* path) {
        a = AAssetManager_open(g_asset_mgr, path, AASSET_MODE_RANDOM);
        if (!a) return false;
        sz = u64(AAsset_getLength64(a));
        return sz > 0;
    }
    ~AssetSource() override {
        if (a) AAsset_close(a);
    }
    bool read_at(u64 off, u8* dst, size_t n) override {
        if (!a) return false;
        if (AAsset_seek64(a, off64_t(off), SEEK_SET) < 0) return false;
        size_t got = 0;
        while (got < n) {
            int r = AAsset_read(a, dst + got, n - got);
            if (r <= 0) return false;
            got += size_t(r);
        }
        return true;
    }
    u64 total() override { return sz; }
};

static JNIEnv* jenv() {
    JNIEnv* e = nullptr;
    if (g_vm) g_vm->AttachCurrentThread(&e, nullptr);
    return e;
}

static void call_void(jmethodID m) {
    JNIEnv* e = jenv();
    if (e && g_activity && m) e->CallVoidMethod(g_activity, m);
}

static void call_void_f(jmethodID m, jfloat v) {
    JNIEnv* e = jenv();
    if (e && g_activity && m) e->CallVoidMethod(g_activity, m, v);
}

static std::string call_str_str(jmethodID m, const std::string& k) {
    JNIEnv* e = jenv();
    if (!e || !g_activity || !m) return "";
    jstring jk = e->NewStringUTF(k.c_str());
    jstring jr = (jstring)e->CallObjectMethod(g_activity, m, jk);
    std::string out;
    if (jr) {
        const char* c = e->GetStringUTFChars(jr, nullptr);
        if (c) {
            out = c;
            e->ReleaseStringUTFChars(jr, c);
        }
        e->DeleteLocalRef(jr);
    }
    e->DeleteLocalRef(jk);
    return out;
}

static void call_str_void(jmethodID m, const std::string& a, const std::string& b) {
    JNIEnv* e = jenv();
    if (!e || !g_activity || !m) return;
    jstring ja = e->NewStringUTF(a.c_str());
    jstring jb = e->NewStringUTF(b.c_str());
    e->CallVoidMethod(g_activity, m, ja, jb);
    e->DeleteLocalRef(ja);
    e->DeleteLocalRef(jb);
}

static void call_bytes(jmethodID m, const u8* d, size_t n) {
    JNIEnv* e = jenv();
    if (!e || !g_activity || !m) return;
    jbyteArray arr = e->NewByteArray(jsize(n));
    e->SetByteArrayRegion(arr, 0, jsize(n), (const jbyte*)d);
    e->CallVoidMethod(g_activity, m, arr);
    e->DeleteLocalRef(arr);
}

static void call_click(const u8* d, size_t n, float vol) {
    JNIEnv* e = jenv();
    if (!e || !g_activity || !m_click) return;
    jbyteArray arr = e->NewByteArray(jsize(n));
    e->SetByteArrayRegion(arr, 0, jsize(n), (const jbyte*)d);
    e->CallVoidMethod(g_activity, m_click, arr, vol);
    e->DeleteLocalRef(arr);
}

} 

using namespace pipeline;

namespace ui {

static void send_pref(const char* k, const std::string& v) {
    call_str_void(m_set_pref, k, v);
}

static void session_clear() {
    call_void(m_session_clear_j);
}

static void play_click() {
    std::vector<u8> pcm;
    audio::synth_click(pcm, app.sfx_vol);
    call_click(pcm.data(), pcm.size(), app.sfx_vol);
}

static bool touch_down(float x, float y);
static bool touch_move(float x, float y);
static void touch_up(float x, float y);

static void handle_touch(int action, float x, float y) {
    if (security::event() != security::EVENT_NONE) return;
    if (app.phase != PHASE_MENU) return;
    if (action == 0) {
        touch_down(x, y);
    } else if (action == 2) {
        touch_move(x, y);
    } else if (action == 1 || action == 3) {
        touch_up(x, y);
    }
}

static void switch_page(int p) {
    if (app.page == p) return;
    app.prev_page = app.page;
    app.page = Page(p);
    app.page_anim = 0.f;
}

static bool touch_down(float x, float y) {
    float dp = app.dp;
    for (int i = 0; i < 4; i++) {
        if (app.tile_rects[i].hit(x / dp, y / dp)) {
            app.press_tile = i;
            app.press_tile_t = 0.f;
            return true;
        }
    }
    if (app.page == PAGE_HOME) {
        Rect* hb[3] = {&app.play_rect, &app.mode_l, &app.mode_r};
        for (int i = 0; i < 3; i++) {
            if (hb[i]->hit(x / dp, y / dp)) {
                app.press_btn = i;
                app.press_btn_t = 0.f;
                return true;
            }
        }
    }
    if (app.page == PAGE_SET) {
        for (int i = 0; i < 3; i++) {
            if (app.tab_rects[i].hit(x / dp, y / dp)) {
                app.press_tab = i;
                app.press_tab_t = 0.f;
                return true;
            }
        }
        if (app.tab == TAB_SOUND) {
            if (app.music_sl.track.hit(x / dp, y / dp)) {
                app.music_sl.dragging = true;
                app.music_sl.value = std::min(std::max((x / dp - app.music_sl.track.x) / app.music_sl.track.w, 0.f), 1.f);
                call_void_f(m_music_vol, app.music_vol);
                return true;
            }
            if (app.sfx_sl.track.hit(x / dp, y / dp)) {
                app.sfx_sl.dragging = true;
                app.sfx_vol = std::min(std::max((x / dp - app.sfx_sl.track.x) / app.sfx_sl.track.w, 0.f), 1.f);
                return true;
            }
        }
        if (app.tab == TAB_MISC) {
            if (app.change_rect.hit(x / dp, y / dp)) {
                app.press_change = true;
                app.press_change_t = 0.f;
                return true;
            }
            if (app.tg_rect.hit(x / dp, y / dp)) {
                app.press_tg = true;
                app.press_tg_t = 0.f;
                return true;
            }
            if (app.logout_rect.hit(x / dp, y / dp)) {
                app.press_logout = true;
                app.press_logout_t = 0.f;
                return true;
            }
        }
    }
    return false;
}

static bool touch_move(float x, float y) {
    float dp = app.dp;
    if (app.music_sl.dragging) {
        app.music_sl.value = std::min(std::max((x / dp - app.music_sl.track.x) / app.music_sl.track.w, 0.f), 1.f);
        app.music_vol = app.music_sl.value;
        call_void_f(m_music_vol, app.music_vol);
        return true;
    }
    if (app.sfx_sl.dragging) {
        float nv = std::min(std::max((x / dp - app.sfx_sl.track.x) / app.sfx_sl.track.w, 0.f), 1.f);
        if (nv != app.sfx_vol) {
            app.sfx_vol = nv;
            play_click();
        }
        return true;
    }
    return false;
}

static void touch_up(float x, float y) {
    float dp = app.dp;
    if (app.press_btn >= 0) {
        int b = app.press_btn;
        app.press_btn = -1;
        Rect* hb[3] = {&app.play_rect, &app.mode_l, &app.mode_r};
        if (hb[b]->hit(x / dp, y / dp)) {
            play_click();
            if (b == 0) {
                app.toast = 2.4f;
            } else if (b == 1) {
                app.mode = (app.mode + 2) % 3;
                app.mode_dir = -1;
                app.mode_anim = 0.f;
            } else {
                app.mode = (app.mode + 1) % 3;
                app.mode_dir = 1;
                app.mode_anim = 0.f;
            }
        }
        return;
    }
    if (app.press_tile >= 0) {
        int i = app.press_tile;
        app.press_tile = -1;
        if (app.tile_rects[i].hit(x / dp, y / dp)) {
            play_click();
            switch_page(i);
        }
        return;
    }
    if (app.press_tab >= 0) {
        int i = app.press_tab;
        app.press_tab = -1;
        if (app.tab_rects[i].hit(x / dp, y / dp)) {
            play_click();
            app.tab = SetTab(i);
            app.page_anim = 0.f;
        }
        return;
    }
    if (app.press_change) {
        app.press_change = false;
        if (app.change_rect.hit(x / dp, y / dp)) {
            play_click();
            app.lang = (app.lang + 1) % 3;
            tr.set_lang(app.lang);
            const char* codes[3] = {"ru", "en", "tr"};
            send_pref("lang", codes[app.lang]);
        }
        return;
    }
    if (app.press_logout) {
        app.press_logout = false;
        if (app.logout_rect.hit(x / dp, y / dp)) {
            play_click();
            ui_stop_music_request();
            session_clear();
            ui_logout_request();
            return;
        }
        return;
    }
    if (app.press_tg) {
        app.press_tg = false;
        if (app.tg_rect.hit(x / dp, y / dp)) {
            play_click();
            call_void(m_tg);
        }
        return;
    }
    if (app.music_sl.dragging || app.sfx_sl.dragging) {
        app.music_sl.dragging = false;
        app.sfx_sl.dragging = false;
        app.music_vol = app.music_sl.value;
        save_volumes();
        return;
    }
}

static void load_prefs() {
    std::string lang = call_str_str(m_pref, "lang");
    if (lang == "en") app.lang = 1;
    else if (lang == "tr") app.lang = 2;
    else if (lang == "ru") app.lang = 0;
    else app.lang = system_language();
    std::string mv = call_str_str(m_pref, "music_volume");
    std::string sv = call_str_str(m_pref, "sfx_volume");
    int mvi = atoi(mv.c_str());
    int svi = atoi(sv.c_str());
    app.music_vol = mvi > 0 ? std::min(float(mvi), 100.f) / 100.f : 0.8f;
    app.sfx_vol = svi >= 0 ? std::min(float(svi), 100.f) / 100.f : 0.8f;
    app.music_sl.value = app.music_vol;
    app.sfx_sl.value = app.sfx_vol;
    tr.set_lang(app.lang);
}

static void step_frame(double dt) {
    app.time += float(dt);
    if (app.phase == PHASE_LOADING) {
        app.shown_progress += (g_progress.load() - app.shown_progress) * std::min(1.f, float(dt) * 8.f);
                if (g_progress.load() >= 100.f && app.fade_in >= 1.f) {
            app.shown_progress = 100.f;
            if (security::event() == security::EVENT_NONE) {
                app.fade_out += float(dt) / 0.45f;
                if (app.fade_out >= 1.f) {
                    app.phase = app.session_valid ? PHASE_MENU : PHASE_AUTH;
                    app.page_anim = 0.f;
                    if (app.phase == PHASE_MENU) ui_start_music_request();
                    else ui_show_auth_request();
                }
            }
        } else {
            app.fade_in += float(dt) / 0.4f;
            if (app.fade_in > 1.f) app.fade_in = 1.f;
        }
        if (g_progress.load() >= 100.f && app.fade_in < 1.f) {
            app.fade_in += float(dt) / 0.2f;
            if (app.fade_in > 1.f) app.fade_in = 1.f;
        }
    } else {
        app.page_anim = std::min(1.f, app.page_anim + float(dt) / 0.22f);
        float hm_target = app.page == PAGE_HOME ? 1.f : 0.f;
        app.home_mix += (hm_target - app.home_mix) * std::min(1.f, float(dt) * 10.f);
        if (app.press_tile >= 0) app.press_tile_t = std::min(1.f, app.press_tile_t + float(dt) / 0.12f);
        if (app.press_tab >= 0) app.press_tab_t = std::min(1.f, app.press_tab_t + float(dt) / 0.12f);
        if (app.press_change) app.press_change_t = std::min(1.f, app.press_change_t + float(dt) / 0.12f);
        if (app.press_tg) app.press_tg_t = std::min(1.f, app.press_tg_t + float(dt) / 0.12f);
        if (app.press_btn >= 0) app.press_btn_t = std::min(1.f, app.press_btn_t + float(dt) / 0.12f);
        if (app.press_logout) app.press_logout_t = std::min(1.f, app.press_logout_t + float(dt) / 0.12f);
        app.mode_anim = std::min(1.f, app.mode_anim + float(dt) / 0.25f);
        app.intro = std::min(6.f, app.intro + float(dt));
        if (app.toast > 0.f) app.toast = std::max(0.f, app.toast - float(dt));
    }
}

static void render_frame(glr::Ctx& c) {
    eglQuerySurface(c.display, c.surface, EGL_WIDTH, &c.vw);
    eglQuerySurface(c.display, c.surface, EGL_HEIGHT, &c.vh);
    app.dp = c.density > 0.f ? c.density : 2.f;
    app.vw = c.vw;
    app.vh = c.vh;
    if (app.vw == 0 || app.vh == 0) return;
    layout();
    dl.clear();
    if (security::event() != security::EVENT_NONE) {
        draw_security_screen();
    } else if (app.phase == PHASE_LOADING) {
        draw_loading();
    } else if (app.phase == PHASE_MENU) {
        draw_menu();
    } else {
        push_shape(0, 0, float(app.vw) / app.dp, float(app.vh) / app.dp, 0.f,
                   0.02f, 0.02f, 0.03f, 1.f, 0.f, 0.f, 0.f, 0.f);
    }
    glViewport(0, 0, c.vw, c.vh);
    float L = 0, R = float(c.vw) / app.dp, B = float(c.vh) / app.dp, T = 0;
    float mvp[16] = {
        2.f / (R - L), 0, 0, 0,
        0, 2.f / (T - B), 0, 0,
        0, 0, -1.f, 0,
        -(R + L) / (R - L), -(T + B) / (T - B), 0, 1.f};
    glClearColor(0.f, 0.f, 0.f, 0.f);
    glClear(GL_COLOR_BUFFER_BIT);
    glBindBuffer(GL_ARRAY_BUFFER, c.vbo);
    if (!dl.shape.empty()) glBufferData(GL_ARRAY_BUFFER, sizeof(float) * dl.shape.size(), dl.shape.data(), GL_STREAM_DRAW);
    glBindBuffer(GL_ARRAY_BUFFER, c.vbo_tex);
    if (!dl.textured.empty()) glBufferData(GL_ARRAY_BUFFER, sizeof(float) * dl.textured.size(), dl.textured.data(), GL_STREAM_DRAW);
    glBindBuffer(GL_ARRAY_BUFFER, c.vbo_text);
    if (!dl.textv.empty()) glBufferData(GL_ARRAY_BUFFER, sizeof(float) * dl.textv.size(), dl.textv.data(), GL_STREAM_DRAW);
    int shape_first = 0, tex_first = 0, text_first = 0;
    for (const DrawList::Item& it : dl.items) {
        int count = it.count;
        if (count <= 0) continue;
        if (it.prog == 0) {
            glUseProgram(c.prog_shape);
            glUniformMatrix4fv(c.u_shape_mvp, 1, GL_FALSE, mvp);
            glUniform2f(c.u_shape_res, float(c.vw), float(c.vh));
            glUniform1f(c.u_shape_dp, app.dp);
            glUniform1f(c.u_shape_time, app.time);
            glUniform1f(c.u_shape_home, app.home_mix);
            glBindBuffer(GL_ARRAY_BUFFER, c.vbo);
            GLsizei stride = 26 * sizeof(float);
            glEnableVertexAttribArray(0);
            glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, stride, (void*)0);
            for (int a = 1; a < 7; a++) {
                glEnableVertexAttribArray(a);
                glVertexAttribPointer(a, 4, GL_FLOAT, GL_FALSE, stride, (void*)((2 + (a - 1) * 4) * sizeof(float)));
            }
            glDrawArrays(GL_TRIANGLES, shape_first, count);
            shape_first += count;
        } else if (it.prog == 1 || it.prog == 3) {
            u32 t = 0;
            if (it.tex == 10) t = c.ls_tex;
            else if (it.tex >= 20 && it.tex < 24) t = c.btn_tex[it.tex - 20];
            if (t) {
                bool icon = it.prog == 3;
                glUseProgram(icon ? c.prog_icon : c.prog_tex);
                glUniformMatrix4fv(icon ? c.u_icon_mvp : c.u_tex_mvp, 1, GL_FALSE, mvp);
                glActiveTexture(GL_TEXTURE0);
                glBindTexture(GL_TEXTURE_2D, t);
                glUniform1i(icon ? c.u_icon_sampler : c.u_tex_sampler, 0);
                glBindBuffer(GL_ARRAY_BUFFER, c.vbo_tex);
                GLsizei stride = 8 * sizeof(float);
                for (int a = 3; a < 7; a++) glDisableVertexAttribArray(a);
                glEnableVertexAttribArray(0);
                glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, stride, (void*)0);
                glEnableVertexAttribArray(1);
                glVertexAttribPointer(1, 2, GL_FLOAT, GL_FALSE, stride, (void*)(2 * sizeof(float)));
                glEnableVertexAttribArray(2);
                glVertexAttribPointer(2, 4, GL_FLOAT, GL_FALSE, stride, (void*)(4 * sizeof(float)));
                glDrawArrays(GL_TRIANGLES, tex_first, count);
            }
            tex_first += count;
        } else {
            glUseProgram(c.prog_text);
            glUniformMatrix4fv(c.u_text_mvp, 1, GL_FALSE, mvp);
            u32 t = tr.page_tex(it.tex);
            glActiveTexture(GL_TEXTURE0);
            glBindTexture(GL_TEXTURE_2D, t);
            glUniform1i(c.u_text_sampler, 0);
            glBindBuffer(GL_ARRAY_BUFFER, c.vbo_text);
            GLsizei stride = 8 * sizeof(float);
            for (int a = 3; a < 7; a++) glDisableVertexAttribArray(a);
            glEnableVertexAttribArray(0);
            glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, stride, (void*)0);
            glEnableVertexAttribArray(1);
            glVertexAttribPointer(1, 2, GL_FLOAT, GL_FALSE, stride, (void*)(2 * sizeof(float)));
            glEnableVertexAttribArray(2);
            glVertexAttribPointer(2, 4, GL_FLOAT, GL_FALSE, stride, (void*)(4 * sizeof(float)));
            glDrawArrays(GL_TRIANGLES, text_first, count);
            text_first += count;
        }
    }
    glBindBuffer(GL_ARRAY_BUFFER, 0);

    if (security::event() != security::EVENT_NONE) {
        static bool auth_hide_sent = false;
        if (!auth_hide_sent) {
            auth_hide_sent = true;
            ui_hide_auth_request();
        }
    }
    if (security::event() == security::EVENT_TAMPER) {
        static bool exit_called = false;
        if (!exit_called) {
            exit_called = true;
            security::shutdown();
            if (request_exit_cb) request_exit_cb();
        }
    }
}

static void process_tex_queue(glr::Ctx& c) {
    std::vector<glr::TexItem> items;
    {
        std::lock_guard<std::mutex> lk(c.tex_mu);
        items.swap(c.tex_queue);
    }
    for (glr::TexItem& t : items) {
        img::Image im;
        if (img::decode_png(t.data.data(), t.data.size(), im)) {
            u32 tex = glr::make_tex_rgba(im.px.data(), int(im.w), int(im.h));
            if (t.slot == 10) {
                c.ls_tex = tex;
                c.ls_w = int(im.w);
                c.ls_h = int(im.h);
            } else if (t.slot >= 20 && t.slot < 24) {
                c.btn_tex[t.slot - 20] = tex;
                c.btn_w[t.slot - 20] = int(im.w);
                c.btn_h[t.slot - 20] = int(im.h);
            }
        }
        t.data.clear();
    }
}

} 

namespace pipeline {

static void set_progress(float p) {
    float cur = g_progress.load();
    while (p > cur) {
        if (g_progress.compare_exchange_weak(cur, p)) break;
    }
}

static bool extract_to_bytes(const char* path, Bytes& out) {
    const vaf::VafEntry* e = g_archive.find(path);
    if (!e) return false;
    return g_archive.extract(*e, out);
}

static void load_thread_fn() {
    AssetSource* src = new AssetSource();
    if (!src->open("assets.vaf")) {
        delete src;
        g_progress = 100.f;
        return;
    }
    if (!g_archive.open(src)) {
        delete src;
        g_progress = 100.f;
        return;
    }
    set_progress(3.f);
    Bytes ls_data;
    if (extract_to_bytes("assets/main/ls.png", ls_data)) {
        {
            std::lock_guard<std::mutex> lk(glr::gl_ctx.tex_mu);
            glr::gl_ctx.tex_queue.push_back({10, std::move(ls_data), 0, 0});
        }
        set_progress(9.f);
    }
    Bytes auth_img;
    if (extract_to_bytes("assets/main/vid.jfif", auth_img)) {
        call_bytes(m_auth_image, auth_img.data(), auth_img.size());
    }
    Bytes font_data;
    if (extract_to_bytes("assets/main/font.ttf", font_data)) {
        g_font_data = std::move(font_data.d);
    }
    Bytes ru_data;
    if (extract_to_bytes("assets/main/ru.ttf", ru_data)) {
        g_font_ru = std::move(ru_data.d);
    }
    Bytes tr_data;
    if (extract_to_bytes("assets/main/tr.ttf", tr_data)) {
        g_font_tr = std::move(tr_data.d);
    }
    g_font_ready = true;
    set_progress(13.f);
    const vaf::VafEntry* snd = g_archive.find("assets/sounds/soundtrack.mp3");
    if (snd) {
        std::string path = g_cache_dir + "/wa_snd_tmp.mp3";
        FILE* f = fopen(path.c_str(), "wb");
        if (f) {
            u64 total = snd->size;
            auto sink = [&](const u8* p, size_t n) -> bool {
                return fwrite(p, 1, n, f) == n;
            };
            auto prog = [&](u64 done) {
                set_progress(13.f + 42.f * float(double(done) / double(total > 0 ? total : 1)));
            };
            bool ok = g_archive.extract_stream(*snd, sink, prog);
            fclose(f);
            if (ok) {
                g_music_path = path;
                set_progress(55.f);
            }
        }
    }
    const char* btns[4] = {"assets/buttons/home.png", "assets/buttons/gun.png",
                           "assets/buttons/chat.png", "assets/buttons/settings.png"};
    for (int i = 0; i < 4; i++) {
        Bytes bd;
        if (extract_to_bytes(btns[i], bd)) {
            std::lock_guard<std::mutex> lk(glr::gl_ctx.tex_mu);
            glr::gl_ctx.tex_queue.push_back({20 + i, std::move(bd), 0, 0});
        }
        set_progress(55.f + 3.5f * float(i + 1));
    }
    const vaf::VafEntry* ag = g_archive.find("assets/main/agent.glb");
    if (!ag) ag = g_archive.find("agent.glb");
    if (ag) {
        std::vector<u8> acc;
        acc.reserve(size_t(ag->size));
        auto sink = [&](const u8* p, size_t n) -> bool {
            acc.insert(acc.end(), p, p + n);
            return true;
        };
        auto prog = [&](u64 done) {
            set_progress(69.f + 27.f * float(double(done) / double(ag->size > 0 ? ag->size : 1)));
        };
        if (g_archive.extract_stream(*ag, sink, prog)) {
            set_progress(96.f);
            call_bytes(m_agent, acc.data(), acc.size());
        } else {
            call_void(m_agent_missing);
        }
    } else {
        set_progress(96.f);
        call_void(m_agent_missing);
    }
    while (!g_agent_done.load() && !g_quit.load()) {
        std::this_thread::sleep_for(std::chrono::milliseconds(30));
    }
    set_progress(100.f);
}

static void start_load_thread() {
    std::thread t(load_thread_fn);
    t.detach();
}

} 

static void native_frame_impl(double time_ms) {
    static double last = 0;
    double dt = last > 0 ? std::min((time_ms - last) / 1000.0, 0.1) : 0.016;
    last = time_ms;
    glr::Ctx& c = glr::gl_ctx;
    if (c.surface == EGL_NO_SURFACE) return;
    ui::process_tex_queue(c);
    if (!ui::app.menu_entered && ui::app.phase == ui::PHASE_MENU) ui::app.menu_entered = true;
    ui::step_frame(dt);
    if (g_font_ready.exchange(false)) {
        ui::tr.load(&c, g_font_data.data(), g_font_data.size(),
                    g_font_ru.data(), g_font_ru.size(), g_font_tr.data(), g_font_tr.size());
        ui::load_prefs();
        secure_wipe(g_font_data.data(), g_font_data.size());
        secure_wipe(g_font_ru.data(), g_font_ru.size());
        secure_wipe(g_font_tr.data(), g_font_tr.size());
        std::vector<u8>().swap(g_font_data);
        std::vector<u8>().swap(g_font_ru);
        std::vector<u8>().swap(g_font_tr);
    }
    if (ui::app.phase == ui::PHASE_LOADING || ui::app.phase == ui::PHASE_MENU || ui::app.phase == ui::PHASE_AUTH) {
        ui::render_frame(c);
        eglSwapBuffers(c.display, c.surface);
    }
}

static void native_surface_impl(JNIEnv* env, jobject surf) {
    glr::Ctx& c = glr::gl_ctx;
    if (surf == nullptr) {
        glr::destroy(c);
        return;
    }
    if (c.win != nullptr) {
        ANativeWindow* newWin = ANativeWindow_fromSurface(env, surf);
        if (newWin != c.win) {
            glr::destroy(c);
            c.win = newWin;
        } else {
            ANativeWindow_release(newWin);
            return;
        }
    } else {
        c.win = ANativeWindow_fromSurface(env, surf);
    }
    if (c.win) {
        if (!glr::init(c, c.win, c.density)) {
            WA_LOG("GL init failed");
            glr::destroy(c);
        }
    }
}

extern "C" JNIEXPORT jint JNICALL JNI_OnLoad(JavaVM* vm, void*) {
    g_vm = vm;
    JNIEnv* e = nullptr;
    if (vm->GetEnv((void**)&e, JNI_VERSION_1_6) != JNI_OK) return JNI_ERR;
    return JNI_VERSION_1_6;
}

extern "C" JNIEXPORT void JNICALL
Java_com_varazdp_wararena_MainActivity_nativeInit(JNIEnv* env, jobject, jobject activity,
                                                  jstring cacheDir, jstring version, jfloat density) {
    env->GetJavaVM(&g_vm);
    if (g_activity) env->DeleteGlobalRef(g_activity);
    g_activity = env->NewGlobalRef(activity);
    jclass cls = env->GetObjectClass(activity);
    m_music_ready = env->GetMethodID(cls, "onNativeMusicReady", "(Ljava/lang/String;)V");
    m_click = env->GetMethodID(cls, "onNativeClick", "([BF)V");
    m_tg = env->GetMethodID(cls, "onNativeTelegram", "()V");
    m_agent = env->GetMethodID(cls, "onNativeAgent", "([B)V");
    m_agent_missing = env->GetMethodID(cls, "onNativeAgentMissing", "()V");
    m_music_vol = env->GetMethodID(cls, "onNativeMusicVolume", "(F)V");
    m_pref = env->GetMethodID(cls, "onNativePref", "(Ljava/lang/String;)Ljava/lang/String;");
    m_set_pref = env->GetMethodID(cls, "onNativeSetPref", "(Ljava/lang/String;Ljava/lang/String;)V");
    m_get_assets = env->GetMethodID(cls, "getAssets", "()Landroid/content/res/AssetManager;");
    m_show_auth = env->GetMethodID(cls, "onNativeShowAuth", "()V");
    m_hide_auth = env->GetMethodID(cls, "onNativeHideAuth", "()V");
    m_start_music = env->GetMethodID(cls, "onNativeStartMusic", "()V");
    m_stop_music = env->GetMethodID(cls, "onNativeStopMusic", "()V");
    m_logout = env->GetMethodID(cls, "onNativeLogout", "()V");
    m_request_exit = env->GetMethodID(cls, "onNativeRequestExit", "()V");
    m_session_get = env->GetMethodID(cls, "onNativeSessionGet", "()Ljava/lang/String;");
    m_session_clear_j = env->GetMethodID(cls, "onNativeSessionClear", "()V");
    m_auth_image = env->GetMethodID(cls, "onNativeAuthImage", "([B)V");

    ui::auth_cb_show = []() { call_void(m_show_auth); };
    ui::auth_cb_hide = []() { call_void(m_hide_auth); };
    ui::auth_cb_start_music = []() { call_void(m_start_music); };
    ui::auth_cb_stop_music = []() { call_void(m_stop_music); };
    ui::auth_cb_logout = []() { call_void(m_logout); };
    ui::request_exit_cb = []() { call_void(m_request_exit); };

    if (m_get_assets && g_activity) {
        jobject am = env->CallObjectMethod(g_activity, m_get_assets);
        if (am) {
            g_asset_mgr = AAssetManager_fromJava(env, am);
            env->DeleteLocalRef(am);
        }
    }
    const char* cd = env->GetStringUTFChars(cacheDir, nullptr);
    if (cd) {
        g_cache_dir = cd;
        env->ReleaseStringUTFChars(cacheDir, cd);
    }
    const char* ver = env->GetStringUTFChars(version, nullptr);
    if (ver) {
        g_version = ver;
        env->ReleaseStringUTFChars(version, ver);
    }
    glr::gl_ctx.density = density;

    {
        JNIEnv* e = jenv();
        if (e && m_session_get) {
            jstring js = (jstring)e->CallObjectMethod(g_activity, m_session_get);
            if (js) {
                const char* c = e->GetStringUTFChars(js, nullptr);
                ui::app.session_valid = c && *c;
                if (c) e->ReleaseStringUTFChars(js, c);
                e->DeleteLocalRef(js);
            }
        }
    }

    ui::load_prefs();
    security::start();
    if (g_asset_mgr) start_load_thread();
}

extern "C" JNIEXPORT void JNICALL
Java_com_varazdp_wararena_MainActivity_nativeSurface(JNIEnv* env, jobject, jobject surface) {
    native_surface_impl(env, surface);
}

extern "C" JNIEXPORT void JNICALL
Java_com_varazdp_wararena_MainActivity_nativeFrame(JNIEnv*, jobject, jdouble timeMs) {
    native_frame_impl(timeMs);
}

extern "C" JNIEXPORT void JNICALL
Java_com_varazdp_wararena_MainActivity_nativeTouch(JNIEnv*, jobject, jint action, jfloat x, jfloat y) {
    ui::handle_touch(action, x, y);
}

extern "C" JNIEXPORT void JNICALL
Java_com_varazdp_wararena_MainActivity_nativeResume(JNIEnv*, jobject) {
}

extern "C" JNIEXPORT void JNICALL
Java_com_varazdp_wararena_MainActivity_nativePause(JNIEnv*, jobject) {
}

extern "C" JNIEXPORT void JNICALL
Java_com_varazdp_wararena_MainActivity_nativeBack(JNIEnv*, jobject) {
    if (ui::app.phase == ui::PHASE_MENU && ui::app.page != ui::PAGE_HOME) {
        ui::play_click();
        ui::switch_page(ui::PAGE_HOME);
    }
}

extern "C" JNIEXPORT void JNICALL
Java_com_varazdp_wararena_MainActivity_nativeAgentDone(JNIEnv*, jobject) {
    g_agent_done = true;
}

extern "C" JNIEXPORT void JNICALL
Java_com_varazdp_wararena_MainActivity_nativeAuthResult(JNIEnv*, jobject, jboolean ok) {
    ui::app.session_valid = ok == JNI_TRUE;
    if (ok) {
        ui::app.phase = ui::PHASE_MENU;
        ui::app.page_anim = 0.f;
        ui::app.intro = 0.f;
        if (ui::auth_cb_start_music) ui::auth_cb_start_music();
    } else {
        ui::app.phase = ui::PHASE_AUTH;
    }
}

extern "C" JNIEXPORT void JNICALL
Java_com_varazdp_wararena_MainActivity_nativeStartMusicFile(JNIEnv*, jobject) {
    if (security::event() != security::EVENT_NONE) return;
    if (g_music_path.empty()) return;
    JNIEnv* e = jenv();
    if (e && g_activity && m_music_ready) {
        jstring jp = e->NewStringUTF(g_music_path.c_str());
        e->CallVoidMethod(g_activity, m_music_ready, jp);
        e->DeleteLocalRef(jp);
    }
}

} 

#else

namespace wa {
void wa_desktop_unused() {}
}

#endif
