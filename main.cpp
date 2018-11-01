#include <iostream>
#include <vector>
#include <cassert>
#include <string>
#include <chrono>
#include <ctime>

/*
Operations: 8000000
Encoder time: 0.870479 s
Decoder time: 1.16962 s
Encoder Speed: 140.233 MBytes/sec
Decoder Speed: 104.368 MBytes/sec
(
 clang version 3.8.0-2ubuntu4 (tags/RELEASE_380/final)
 Target: x86_64-pc-linux-gnu
)
 */

std::string to_string(__uint128_t x) {
    std::string s;
    __uint128_t mask = 0xf;
    for (int i = 31; i >= 0; --i) {
        uint8_t block = static_cast<uint8_t>((x & (mask << (i * 4))) >> (i * 4));
        char c = ((block < 10) ? ('0' + block) : ('a' + static_cast<uint8_t>(block - 10)));
        s += c;
    }
    return s;
}

__uint128_t from_string(std::string s) {
    __uint128_t result = 0;
    for (size_t i = 0; i < 32; ++i) {
        __uint128_t block = static_cast<__uint128_t>((s[i] < 'a') ? (s[i] - '0') : (s[i] - 'a' + 10));
        result = (result << 4) + block;
    }
    return result;
}

template <int k>
class GPolynom{
public:
    GPolynom() = default;
    explicit GPolynom(uint8_t v) {
        for (size_t i = 0; i < k; ++i) {
            koef[i] = v & 1;
            v = (v >> 1);
        }
    }
    int to_int() const {
        int result = 0;
        for (int i = k - 1; i >= 0; --i) {
            result = (result << 1) + koef[i];
        }
        return result;
    }
    std::vector<int> koef = std::vector<int>(k, 0);
    const GPolynom operator+(const GPolynom& rv) const {
        GPolynom p;
        for (size_t i = 0; i < k; ++i) {
            p.koef[i] = (koef[i] + rv.koef[i]) & 1;
        }
        return p;
    }
    const GPolynom operator*(const GPolynom& rv) const {
        // p(x) = x 8 + x 7 + x 6 + x + 1
        std::vector<uint8_t> t(k * 2, 0);
        for (size_t i = 0; i < k; ++i) {
            for (size_t j = 0; j < k; ++j) {
                t[i + j] = (t[i + j] + koef[i] * rv.koef[j]) & 1;
            }
        }

        for (int i = 2 * k - 1; i >= k; --i) {
            if (t[i]) {
                for (int j = i; j >= i - k; --j) {
                    if ((j - i + k == 7) || (j - i + k == 6) || (j -i + k == 1) || (j - i + k == 0)) {
                        t[j] = (t[j] + 1) & 1;
                    }
                }
            }
        }

        GPolynom<k> p;
        for (size_t i = 0; i < k; ++i) {
            p.koef[i] = t[i];
        }
        return p;
    }
};


class Kuznyechik{
 public:
    Kuznyechik() {
        for (size_t i = 0; i < 256; ++i) {
            nonlinear_backward[nonlinear_forward[i]] = static_cast<uint8_t>(i);
        }

        for (size_t i = 0; i < 16; ++i) {
            for (size_t a = 0; a < 256; ++a) {
                l_precalc[i][a] = static_cast<uint8_t>((GPolynom<8>(l_koefs[i])
                        * GPolynom<8>(static_cast<uint8_t>(a))).to_int());
            }
        }
    }

    uint8_t l(__uint128_t a) {
        uint8_t p = 0;
        for (int i = 15 ; i >= 0; --i) {
            p ^= l_precalc[i][static_cast<uint8_t>(a)];
            a >>= 8;
        }
        return p;
    }

    inline __uint128_t X_k(__uint128_t x, __uint128_t k) {
        return x ^ k;
    }

    __uint128_t S(__uint128_t x) {
        __uint128_t result = 0;

        for (size_t i = 0; i < 16; ++i) {
            result += static_cast<__uint128_t>(nonlinear_forward[static_cast<uint8_t>(x)]) << (i * 8);
            x >>= 8;
        }
        return result;
    }

    __uint128_t S_backward(__uint128_t x) {
        __uint128_t result = 0;

        for (size_t i = 0; i < 16; ++i) {
            result += static_cast<__uint128_t>(nonlinear_backward[static_cast<uint8_t>(x)]) << (i * 8);
            x >>= 8;
        }
        return result;
    }

    __uint128_t R(__uint128_t x) {
        return (static_cast<__uint128_t>(l(x)) << (128 - 8)) + (x >> 8);
    }

    __uint128_t L_slow(__uint128_t x) {
        for (size_t i = 0; i < 16; ++i) {
            x = R(x);
        }
        return x;
    }

    __uint128_t R_backward(__uint128_t x) {
        __uint128_t shifted = (x << 8) + (x >> 8 * (15));
        return (x << 8) + static_cast<__uint128_t>(l(shifted));
    }

    __uint128_t L_backward_slow(__uint128_t x) {
        for (size_t i = 0; i < 16; ++i) {
            x = R_backward(x);
        }
        return x;
    }

    void key_extension(__uint128_t a1, __uint128_t a0) {
        std::vector<__uint128_t> C_i;
        K_i = {a1, a0};

        for (size_t i = 1; i <= 32; ++i) {
            C_i.push_back(L_slow(static_cast<__uint128_t>(i)));
        }

        for (size_t i = 0; i < 4; ++i) {
            __uint128_t K_0 = K_i[K_i.size() - 2];
            __uint128_t K_1 = K_i[K_i.size() - 1];
            for (size_t j = 0; j < 8; ++j) {
                auto res = F_k(K_0, K_1, C_i[8 * i + j]);
                K_0 = res.first;
                K_1 = res.second;
            }
            K_i.push_back(K_0);
            K_i.push_back(K_1);
        }

        for (size_t i = 0; i < 16; ++i) {
            for (size_t a = 0; a < 256; ++a) {
                L_precalc[i][a] = L_slow(static_cast<__uint128_t>(a) << (i * 8));
            }
        }

        for (size_t i = 0; i < 16; ++i) {
            for (size_t a = 0; a < 256; ++a) {
                L_backward_precalc[i][a] = L_backward_slow(static_cast<__uint128_t>(a) << (i * 8));
            }
        }

        for (size_t i = 0; i < 16; ++i) {
            for (size_t a = 0; a < 256; ++a) {
                __uint128_t S_a = nonlinear_forward[a];
                LS_precalc[i][a] = L_slow(S_a << (i * 8));
            }
        }

        /// X_0SLX_1SLX_2SLX_3SLX_4SLX_5SLX_6SLX_7SLX_8SLX_9
        for (size_t i = 0; i < 16; ++i) {
            for (size_t a = 0; a < 256; ++a) {
                __uint128_t S_a = nonlinear_backward[a];
                LS_backward_precalc[i][a] = L_backward_slow(S_a << (i * 8));
            }
        }

        for (size_t i = 0; i < 10; ++i) {
            L_backward_k_i_precalc[i] = L_backward_slow(K_i[i]);
        }
    }

    __uint128_t L(__uint128_t x) {
        __uint128_t result = 0;
        for (size_t i = 0; i < 16; ++i) {
            result ^= L_precalc[i][static_cast<uint8_t>(x)];
            x >>= 8;
        }
        return result;
    }

    __uint128_t L_backward(__uint128_t x) {
        __uint128_t result = 0;
        for (size_t i = 0; i < 16; ++i) {
            result ^= L_backward_precalc[i][static_cast<uint8_t>(x)];
            x >>= 8;
        }
        return result;
    }

    std::pair<__uint128_t, __uint128_t> F_k(__uint128_t a1, __uint128_t a0, __uint128_t k) {
        // (a 1 , a 0 ) = (LSX[k](a 1 ) ⊕ a 0 , a 1 ),
        return std::make_pair(L_slow(S(X_k(a1, k))) ^ a0, a1);
    }

    __uint128_t encode(__uint128_t x) {
        for (size_t i = 0; i < 9; ++i) {
            __uint128_t temp = x ^ K_i[i];
            x = 0;
            for (size_t j = 0; j < 16; ++j) {
                x ^= LS_precalc[j][static_cast<uint8_t>(temp)];
                temp >>= 8;
            }
        }
        return x ^ K_i[9];
    }

    __uint128_t decode(__uint128_t x) {
        x = L_backward(x ^ K_i[9]);
        for (size_t i = 8; i >= 1; --i) {
            __uint128_t temp = x;
            x = L_backward_k_i_precalc[i];
            for (size_t j = 0; j < 16; ++j) {
                x ^= LS_backward_precalc[j][static_cast<uint8_t>(temp)];
                temp >>= 8;
            }
        }
        /// X_0SLX_1SLX_2SLX_3SLX_4SLX_5SLX_6SLX_7SLX_8SLX_9
        return S_backward(x) ^ K_i[0];
    }

    std::vector<__uint128_t> K_i;
    const uint8_t nonlinear_forward[256] = {
        252, 238, 221, 17, 207, 110, 49, 22, 251, 196, 250, 218, 35, 197, 4, 77, 233,
        119, 240, 219, 147, 46, 153, 186, 23, 54, 241, 187, 20, 205, 95, 193, 249, 24, 101,
        90, 226, 92, 239, 33, 129, 28, 60, 66, 139, 1, 142, 79, 5, 132, 2, 174, 227, 106, 143,
        160, 6, 11, 237, 152, 127, 212, 211, 31, 235, 52, 44, 81, 234, 200, 72, 171, 242, 42,
        104, 162, 253, 58, 206, 204, 181, 112, 14, 86, 8, 12, 118, 18, 191, 114, 19, 71, 156,
        183, 93, 135, 21, 161, 150, 41, 16, 123, 154, 199, 243, 145, 120, 111, 157, 158, 178,
        177, 50, 117, 25, 61, 255, 53, 138, 126, 109, 84, 198, 128, 195, 189, 13, 87, 223,
        245, 36, 169, 62, 168, 67, 201, 215, 121, 214, 246, 124, 34, 185, 3, 224, 15, 236,
        222, 122, 148, 176, 188, 220, 232, 40, 80, 78, 51, 10, 74, 167, 151, 96, 115, 30, 0,
        98, 68, 26, 184, 56, 130, 100, 159, 38, 65, 173, 69, 70, 146, 39, 94, 85, 47, 140, 163,
        165, 125, 105, 213, 149, 59, 7, 88, 179, 64, 134, 172, 29, 247, 48, 55, 107, 228, 136,
        217, 231, 137, 225, 27, 131, 73, 76, 63, 248, 254, 141, 83, 170, 144, 202, 216, 133,
        97, 32, 113, 103, 164, 45, 43, 9, 91, 203, 155, 37, 208, 190, 229, 108, 82, 89, 166,
        116, 210, 230, 244, 180, 192, 209, 102, 175, 194, 57, 75, 99, 182
    };
    uint8_t nonlinear_backward[256];

    const uint8_t l_koefs[16] = {
            148, 32, 133, 16, 194, 192, 1, 251, 1, 192, 194, 16, 133, 32, 148, 1
    };
    uint8_t l_precalc[16][256];

    __uint128_t L_precalc[16][256];
    __uint128_t L_backward_precalc[16][256];

    __uint128_t LS_precalc[16][256];
    __uint128_t LS_backward_precalc[16][256];

    __uint128_t L_backward_k_i_precalc[10];
};

void measure() {
    Kuznyechik s;
    s.key_extension(from_string("8899aabbccddeeff0011223344556677"), from_string("fedcba98765432100123456789abcdef"));
    size_t iter_count = 8000000;

    __uint128_t res = 0;

    clock_t start_enc = clock();
    for (size_t i = 0; i < iter_count; ++i) {
        res = s.encode(res);
    }
    clock_t end_enc = clock();


    clock_t start_dec = clock();
    for (size_t i = 0; i < iter_count; ++i) {
        res = s.decode(res);
    }
    clock_t end_dec = clock();

    // 128 бит -> 16 байт
    // здесь 32 байта

    double seconds_enc = (double)(end_enc - start_enc) / CLOCKS_PER_SEC;
    double seconds_dec = (double)(end_dec - start_dec) / CLOCKS_PER_SEC;

    // std::cout << to_string(res) << "\n";
    assert(res == 0);
    size_t bytes = 16 * iter_count;
    std::cout << "Operations: " << iter_count << "\n";

    std::cout << "Encoder time: " << seconds_enc << " s\n";
    std::cout << "Decoder time: " << seconds_dec << " s\n";
    std::cout << "Encoder Speed: " << double(bytes) / seconds_enc / 1024 / 1024 << " MBytes/sec\n";
    std::cout << "Decoder Speed: " << double(bytes) / seconds_dec / 1024 / 1024 << " MBytes/sec\n";
}

void self_check() {
    Kuznyechik s;
    s.key_extension(from_string("8899aabbccddeeff0011223344556677"), from_string("fedcba98765432100123456789abcdef"));
    std::vector<std::string> K_i_true = {
            "8899aabbccddeeff0011223344556677",
            "fedcba98765432100123456789abcdef",
            "db31485315694343228d6aef8cc78c44",
            "3d4553d8e9cfec6815ebadc40a9ffd04",
            "57646468c44a5e28d3e59246f429f1ac",
            "bd079435165c6432b532e82834da581b",
            "51e640757e8745de705727265a0098b1",
            "5a7925017b9fdd3ed72a91a22286f984",
            "bb44e25378c73123a5f32f73cdb6e517",
            "72e9dd7416bcf45b755dbaa88e4a4043"
    };

    for (size_t i = 0; i < 10; ++i) {
        assert(to_string(s.K_i[i]) == K_i_true[i]);
    }


    assert(s.X_k(1, 3) == 2);
    assert(s.nonlinear_backward[s.nonlinear_forward[255]] == 255);
    assert(s.S_backward(s.S(1)) == 1);
    assert(s.S_backward(s.S(173434234)) == 173434234);
    assert(to_string(255) == "000000000000000000000000000000ff");
    assert(to_string(from_string("0000000ad000000000000000000000ff")) == "0000000ad000000000000000000000ff");

    assert(to_string(s.S(from_string("ffeeddccbbaa99881122334455667700"))) == "b66cd8887d38e8d77765aeea0c9a7efc");
    assert(to_string(s.S(from_string("b66cd8887d38e8d77765aeea0c9a7efc"))) == "559d8dd7bd06cbfe7e7b262523280d39");
    assert(to_string(s.S(from_string("559d8dd7bd06cbfe7e7b262523280d39"))) == "0c3322fed531e4630d80ef5c5a81c50b");
    assert(to_string(s.S(from_string("0c3322fed531e4630d80ef5c5a81c50b"))) == "23ae65633f842d29c5df529c13f5acda");

    assert(to_string(s.R(from_string("00000000000000000000000000000100"))) == "94000000000000000000000000000001");
    assert(to_string(s.R(from_string("94000000000000000000000000000001"))) == "a5940000000000000000000000000000");
    assert(to_string(s.R(from_string("a5940000000000000000000000000000"))) == "64a59400000000000000000000000000");
    assert(to_string(s.R(from_string("64a59400000000000000000000000000"))) == "0d64a594000000000000000000000000");

    assert(to_string(s.L(from_string("64a59400000000000000000000000000"))) == "d456584dd0e3e84cc3166e4b7fa2890d");
    assert(to_string(s.L(from_string("d456584dd0e3e84cc3166e4b7fa2890d"))) == "79d26221b87b584cd42fbc4ffea5de9a");
    assert(to_string(s.L(from_string("79d26221b87b584cd42fbc4ffea5de9a"))) == "0e93691a0cfc60408b7b68f66b513c13");
    assert(to_string(s.L(from_string("0e93691a0cfc60408b7b68f66b513c13"))) == "e6a8094fee0aa204fd97bcb0b44b8580");


    assert(to_string(s.R_backward(from_string("0d64a594000000000000000000000000")))
                                    == "64a59400000000000000000000000000");

    assert(to_string(s.R_backward(s.R(from_string("0e93691a0cfc60408b7b68f66b513c13"))))
                                    == "0e93691a0cfc60408b7b68f66b513c13");

    assert(to_string(s.L_backward(from_string("e6a8094fee0aa204fd97bcb0b44b8580")))
                                    == "0e93691a0cfc60408b7b68f66b513c13");

    assert(to_string(s.L_backward(s.L(from_string("64a59400000000000000000000000000"))))
                                    == "64a59400000000000000000000000000");

    __uint128_t k1 = from_string("8899aabbccddeeff0011223344556677");
    assert(s.F_k(from_string("1122334455667700ffeeddccbbaa9988"), 0, k1).first
                == from_string("e297b686e355b0a1cf4a2f9249140830"));


    assert(to_string(s.encode(from_string("1122334455667700ffeeddccbbaa9988"))) == "7f679d90bebc24305a468d42b9d4edcd");
    assert(to_string(s.decode(from_string("7f679d90bebc24305a468d42b9d4edcd"))) == "1122334455667700ffeeddccbbaa9988");


    assert(to_string(s.L_backward(234123412341) ^ s.L_backward(432413241))
        == to_string(s.L_backward(234123412341 ^ 432413241)));
}

int main() {
    self_check();
    measure();
    return 0;
}