#include<bits/stdc++.h>
using namespace std;
#define int long long
#define ll __int128
#define mp make_pair
#define pb push_back
#define all(v) v.begin(),v.end()
#define LOCAL

#include <bits/stdc++.h>
using namespace std;

#define elif else if
#define fore(i,a,b) for(int i=a;i<b;i++)

int dx[] = {0, 0, 1, -1, 1, -1, 1, -1};
int dy[] = {1, -1, 0, 0, 1, -1, -1, 1};
int dx4[] = {0, 0, 1, -1};
int dy4[] = {1, -1, 0, 0};
const ll INF = 1e18;
const int INF32 = 1e9 + 7, N = 1e6 + 10, K = 22;
const int mod9 = 1e9 + 9, P1 = 239, P2 = 4933;

void solve();

void testCase() {
    solve();
}

int32_t main() {
    ios::sync_with_stdio(0); cin.tie(0); cout.tie(0);
    int T = 1;
    cin >> T;
    for (int t = 1; t <= T; t++) {
        testCase();
    }
    return 0;
}

namespace fibonacci {
    mt19937_64 rng = mt19937_64(chrono::steady_clock::now().time_since_epoch().count());
    uniform_int_distribution<ll> dist1, dist2;

    ll random(ll a, ll b) {
        return dist1(rng = mt19937_64(rng())) % (b-a+1) + a;
    }

    struct Matrix {
        vector<vector<ll>> v;
        int n;

        Matrix(int x, int y, ll val = 0) {
            v.assign(x, vector<ll>(y, val));
            n = x;
        }

        Matrix mul(Matrix &b, ll mod) {
            Matrix product(n, n);
            for (int i = 0; i < n; i++) {
                for (int k = 0; k < n; k++) {
                    for (int j = 0; j < n; j++) {
                        product.v[i][j] += (__int128)v[i][k] * b.v[k][j] % mod;
                        if (product.v[i][j] >= mod) product.v[i][j] -= mod;
                    }
                }
            }
            return product;
        }

        static Matrix power(Matrix A, ll p, ll mod) {
            Matrix ans = A;
            for (int i = 0; i < A.n; i++) ans.v[i][i] = 1;
            while (p) {
                if (p & 1) ans = ans.mul(A, mod);
                A = A.mul(A, mod);
                p >>= 1;
            }
            return ans;
        }
    };

    ll gcd(ll a, ll b) {
        while (b) {
            ll temp = a % b;
            a = b;
            b = temp;
        }
        return a;
    }

    ll lcm(ll a, ll b) {
        return a / gcd(a, b) * b;
    }

    ll binPower(ll base, ll e, ll mod) {
        ll result = 1;
        base %= mod;
        while (e > 0) {
            if (e & 1) result = (__int128) result * base % mod;
            base = (__int128) base * base % mod;
            e >>= 1;
        }
        return result;
    }

    bool checkComposite(ll n, ll a, ll d, int s) {
        ll x = binPower(a, d, n);
        if (x == 1 || x == n - 1) return false;
        for (int r = 1; r < s; r++) {
            x = (__int128) x * x % n;
            if (x == n - 1) return false;
        }
        return true;
    }

    bool isPrime(ll n) {
        if (n < 2) return false;
        int r = 0;
        ll d = n - 1;
        while ((d & 1) == 0) {
            d >>= 1;
            r++;
        }
        for (int a : {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}) {
            if (n == a) return true;
            if (checkComposite(n, a, d, r)) return false;
        }
        return true;
    }

    ll brent(ll n) {
        if (n % 2 == 0) return 2;
        ll y = random(1, n - 1), c = random(1, n - 1), m = random(1, n - 1);
        ll g = 1, r = 1, q = 1;
        ll x, ys;
        while (g == 1) {
            x = y;
            for (ll i = 0; i < r; i++) {
                y = ((__int128)y * y + c) % n;
            }
            ll k = 0;
            while (k < r && g == 1) {
                ys = y;
                for (ll i = 0; i < min(m, r - k); i++) {
                    y = ((__int128)y * y + c) % n;
                    q = (__int128)q * abs(x - y) % n;
                }
                g = gcd(q, n);
                k += m;
            }
            r *= 2;
        }
        if (g == n) {
            while (true) {
                ys = ((__int128)ys * ys + c) % n;
                g = gcd(abs(x - ys), n);
                if (g > 1) break;
            }
        }
        return g;
    }

    vector<pair<ll, int>> factor(ll n) {
        vector<pair<ll, int>> ret;
        vector<ll> vals;
        while (n > 1) {
            if (isPrime(n)) {
                vals.pb(n);
                break;
            }
            ll x = brent(n);
            while (n % x == 0) n /= x, vals.pb(x);
        }
        sort(all(vals));
        for (ll x : vals) {
            if (!ret.empty() && ret.back().first == x) ret.back().second++;
            else ret.pb({x, 1});
        }
        return ret;
    }

    ll getPisanoPeriod(ll m) {
        ll pis = 1;
        auto fact = factor(m);
        for (auto &f : fact) {
            ll p = f.first;
            ll base = p;
            for (int j = 1; j < f.second; j++) base *= p;
            pis = lcm(pis, getPisanoPeriod(p));
        }
        return pis;
    }

    ll fib(ll n, ll mod) {
        return fibonacci::fib0(n, mod).v[0][0];
    }

    ll fibSum(ll n, ll mod) {
        ll k = n + 2, pisano = getPisanoPeriod(mod);
        k %= pisano;
        ll ans = fib(k, mod) - 1;
        if (ans < 0) ans += mod;
        return ans;
    }

    Matrix fib0(ll n, ll mod) {
        Matrix trans(2, 2), base(2, 1);
        trans.v = {{1, 1}, {1, 0}};
        base.v = {{1}, {0}};
        return Matrix::power(trans, n, mod).mul(base, mod);
    }
}

void solve() {
    int n;
    cin >> n;
    cout << fibonacci::fib0(n, mod9).v[0][0] << endl;
}
