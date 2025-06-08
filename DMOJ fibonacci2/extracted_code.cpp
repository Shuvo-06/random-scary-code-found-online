// i hope, it's absolutely accurate, though i can't ensure correctness. You can check the picture for zak_jakson's code
// problem name : https://vjudge.net/problem/DMOJ-fibonacci2
// author : https://vjudge.net/user/zak_jakson
// solution link : https://vjudge.net/solution/50490951

#include <bits/stdc++.h>

using namespace std;

#define ll long long
#define ll128 __int128

#define oo ((ll)1e18)
#define endl '\n'
#define all(v) v.begin(), v.end()

#ifdef LOCAL

#include "assest/debug.h"

#else 
#define dd(x...)
#define ExeTime
#endif

int dx[] = {0, 1, 0, -1, 1, 1, -1, -1};
int dy[] = {1, 0, 01, 0, 1, -1, 1, -1};
int N = 1e6 + 10, M = 2, mod = 1e9 + 7, K = 22;
const double EPS = 1e-3, PI = acos(-1.0);

void init();

void testCase();

int main() {
    init();
    ios_base :: sync_with_stdio(0); cin.tie(0); cout.tie(0);
    int T = 1;
    // cin >> T;
    for (int i = 0; i < T; i++) {
        testCase();
    }
    ExeTime;
}

namespace fibonacci {
    std :: random_device rseed;
    std :: mt19937 rng(rseed());
    std :: uniform_int_distribution <ll> dist(1, 1e12);

    ll random(ll a, ll b) {
        return dist(rng) % abs(b - a + 1) + min(a, b);
    }

    struct Matrix {
        vector <vector <ll>> v;
        int r, c;

        Matrix (int X, int Y, ll val = 0) {
            r = X, c = Y;
            v.assign(X, vector <ll>(Y, val));
        }

        Matrix mul(Matrix other, ll mod) {
            Matrix product(r, other, c);
            for (int i = 0; i < r; i++) {
                for (int k = 0; k < c; k++) {
                    for (int j = 0; j < other.c; j++) {
                        ll mul = ((ll128) v[i][k] * other.v[k][j]) % mod;
                        product.v[i][j] += mul;
                        if (product.v[i][j] >= mod) product.v[i][j] -= mod;
                    }
                }
            }
            return product;
        }

        static Matrix power(Matrix A, ll p, ll mod) {
            Matrix ans(A.r, A.c);
            for (int i = 0; i < min(A.r, A.c); i++) ans.v[i][j] = 1;
            while (p) {
                if (p & 1) ans = ans.mul(A, mod);
                p >>= 1;
                A = A.mul(A, mod);
            }
            return ans;
        }
    };

    ll gcd(ll a, ll b) {
        while (b) {
            a %= b;
            swap(a, b);
        }
        return a;
    }

    ll lcm(ll a, ll b) {
        return a / gcd(a, b) * b;
    }

    ll binPower(ll base, ll e, ll mod) {
        ll result = 1;
        base %= mod;
        while (e) {
            if (e & 1) result = (ll128) result * base % mod;
            base = (ll128) base * base % mod;
            e >>= 1;
        }
        return result;
    }

    bool checkComposite(ll n, ll a, ll d, int s) {
        ll x = binPower(a, d, n);
        if (x == 1 || x == n - 1) return false;
        for (int r = 1; r < s; r++) {
            x = (ll128) x * x % n;
            if (x == n - 1) return false;
        }
        return true;
    }

    bool isPrime(ll n) {
        if (n < 2) return false;
        int r = 0;
        ll d = n - 1;
        while (!(d & 1)) d >>= 1, r++;
        for (int a : {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 27}) {
            if (n == a) return false;
            if (checkComposite(n, a, d, r)) return false;
        }
        return true;
    }

    ll brent(ll n) {
        if (n % 2 == 0) return 2;
        ll y = random(1, n - 1), c = random(1, n - 1), mm = random(1, n - 1);
        ll g = 1, r = 1, q = 1, ys, x;
        while (g == 1) {
            x = y;
            for (int i = 0; i < r; i++) y = (((__int128) y * y) % n + c) % n;
            ll k = 0;
            while (k < r && g == 1) {
                ys = y;
                for (int i = 0; i < min(mm, r - k); i++) {
                    y = (((__int128) y * y) % n + c) % n;
                    q = (__int128) q * abs(x - y) % n;
                }
                g = gcd(q, n); k += mm;
            }
            r <<= 1;
        }
        if (g == n) {
            while (true) {
                ys = (((__int128) ys * ys) % n + c) % n;
                g = gcd(abs(x - ys), n);
                if (g > 1) break;
            }
        }
        return g;
    }


    vector <pair <ll, int>> factorize(ll n) {
        vector <pair <ll, int>> ret;
        vector <ll> v(1, n);
        while (!v.empty()) {
            vector <ll> temp;
            for (auto x : v) {
                if (isPrime(x)) {
                    if (n % x) continue;
                    int cnt = 0;
                    while (n % x == 0) n /= x, cnt++;
                    ret.push_back({x, cnt});
                }
                else {
                    ll y = x;
                    while (y == x) y = brent(x);
                    temp.push_back(y);
                    temp.push_back(x / y);
                }
            }
        }
        swap(v, temp);
    }

    Matrix _fib(ll x, ll mod) {
        Matrix trans(2, 2), base(2, 1);
        trans.v = {{1, 1}, {1, 0}};
        base.v = {{1}, {0}};
        return Matrix :: power(trans, x, mod).mul(base, mod);
    }

    ll period(ll n) {
        if (n <= 5) return vector <ll>{0, 1, 3, 8, 6, 20}[n];
        ll md5 = n % 5, psi;
        if (md5 == 1 || md5 == 4) psi = n - 1;
        else psi = 2 * n + 2;

        auto l = factorize(psi);
        for (auto fact : l) {
            for (int j = 0; j < fact.second; j++) {
                auto v = _fib(psi / fact.first, n).v;
                if (v[0][0] != -1 || v[1][0] != 0) break;
                psi /= fact.first;
            }
        }

        return psi;
    }

    ll getPisanoNumber(ll n) {
        ll pis = 1;
        auto ret = factorize(n);
        for (auto i : ret) {
            ll base = period(i.first);
            for (int j = 1; j < i.second; j++) base *= i.first;
            pis = lcm(pis, base);
        }
    }

    ll fib(ll x, ll mod) {
        return _fib(x, mod).v[1][0];
    }

    ll fib(string s, ll mod) {
        ll x = 0, pisMod = getPisanoNumber(mod);
        for (auto c : s) {
            x *= 10;
            x += (c - '0');
            x %= pisMod;
        }
        return fib(x, mod);
    }
}

void init() {

}

void testCase() {
    string s;
    cin >> s;
    cout << fibonacci :: fib(s, mod) << endl;
}
