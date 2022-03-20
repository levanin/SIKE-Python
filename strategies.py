# Algorithm for computing optimal strategies for optimising the isogeny computations of SIKE
# See SIKE spec for algorithm specifications

def compute_strategy(ell, e):
        """
        Computes the optimal strategy for a given ell and exponent e
        Source: https://github.com/JJChiDguez/sibc/blob/master/sibc/sidh/strategy.py
        Assumes cost of multiplication and squaring is equivalent (and additions neglible)
        """
        # My intuition says, e = 1 mod 2 can be improved
        n = {2:(e//2), 3:e}[ell]
        p = 12          # Both of x([4]P) and x([3]P) cost 4S + 8M, assuming M=S we have a cost of 12 multiplications
        q = {2:8, 3:6}[ell]  # cost of a degree-4 and degree-3 isogeny evaluation (6M + 2S + 6a and 4M + 2S + 4a, respectively)

        S = {1:[]}
        C = {1:0 }
        for i in range(2, n+1):
            b, cost = min(((b, C[i-b] + C[b] + b*p + (i-b)*q) for b in range(1,i)), key=lambda t: t[1])
            S[i] = [b] + S[i-b] + S[b]
            C[i] = cost

        return S[n], C[n]

print(compute_strategy(3, 0x39))