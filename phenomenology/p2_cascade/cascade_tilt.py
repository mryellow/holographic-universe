#!/usr/bin/env python3
"""P2: does cascading gravity (a 6D embedding of the 5D bulk) give the observed red tilt?

See README.md in this directory for the derivation. In short, for static sources in the 5D bulk
with 4D spatial wavenumber K, linear cascading gravity changes the metric response in two ways:

  1. the propagator 1/K^2 becomes 1/(K^2 + m K), m ~ M6^4 / M5^3 (gravity becomes 6D in the IR);
  2. the tensor structure changes from that of a massless 5D graviton, T_mn - (1/3) eta_mn T, to
     that of a massive one, T_mn - (1/4) eta_mn T (the brane-bending scalar couples to T).

Vainshtein screening restores (2) to the massless form at large K (short distances).

For a fluid with sound speed c^2 = dp/drho in 4 space dimensions this gives, per unit
16 pi G_b drho / (K^2 + m K):

  Newtonian potential (h_00):     massless 1 - (1 - 4c^2)/3,   massive 1 - (1 - 4c^2)/4
  spatial potential   (h_ab):     massless (1 - c^2)/3,        massive 1/4

The paper's zeta = -Phi_4 is the spatial potential. Its ratio massive/massless is
3 / (4 (1 - c^2)) <= 1 for 0 <= c^2 <= 1/4, with equality only for radiation (c^2 = 1/4, the
paper's atmosphere). So both effects make zeta weaker in the infrared: the brane spectrum is
blue at every scale. Part A checks this; Part B asks what an IR boost of the Newtonian type
would have to look like to fit Planck, as a guide for other extensions.

Usage:  uv run python p2_cascade/cascade_tilt.py      (from phenomenology/)
"""
import numpy as np
from scipy.integrate import quad

# Planck 2018; same numbers and sources as p1_jeans/jeans_tilt.py.
NS, SIG_NS = 0.9649, 0.0042
ALPHA, SIG_ALPHA = -0.0045, 0.0067
BETA, SIG_BETA = 0.022, 0.012
K_LO, K_HI, K_PIV = 0.008, 0.1, 0.05
LNP_PL = (NS - 1.0) * np.log(K_HI / K_LO)
SIG_LNP = SIG_NS * np.log(K_HI / K_LO)
CHI2_2SIGMA_2DOF = 6.18


# --- tensor structure -------------------------------------------------------------------------

def newtonian(c2, lam):
    """h_00 per unit 16 pi G drho / K^2, for tensor structure T_mn - lam eta_mn T."""
    return 1.0 - lam * (1.0 - 4.0 * c2)


def spatial(c2, lam):
    """Coefficient of delta_ab in h_ab, same units."""
    return c2 + lam * (1.0 - 4.0 * c2)


def spatial_ratio(c2):
    """zeta amplitude, massive (unscreened cascading) over massless (5D GR)."""
    return spatial(c2, 0.25) / spatial(c2, 1.0 / 3.0)


def newtonian_ratio(c2):
    return newtonian(c2, 0.25) / newtonian(c2, 1.0 / 3.0)


# --- projection onto the brane (Eq. 48) --------------------------------------------------------

def project(F, y):
    """I(y) = int dx (1 + x^2)^-2 F(y sqrt(1 + x^2)): the brane spectrum at y = k/K_*."""
    w = lambda x: (1.0 + x * x) ** -2 * F(y * np.sqrt(1.0 + x * x))
    return 2.0 * quad(w, 0.0, np.inf, limit=400, epsabs=0.0, epsrel=1e-11)[0]


def lnI(F, y):
    return np.log(project(F, y))


def derivs(F, y, h=2e-3):
    """n_s - 1, alpha_s, beta_s at y, by central differences of ln I in ln y."""
    f = [lnI(F, y * np.exp(j * h)) for j in (-2, -1, 0, 1, 2)]
    n1 = (f[3] - f[1]) / (2 * h)
    a = (f[3] - 2 * f[2] + f[1]) / h**2
    b = (f[4] - 2 * f[3] + 2 * f[1] - f[0]) / (2 * h**3)
    return n1, a, b


# --- Part A: the cascading factor for zeta ----------------------------------------------------

def cascade_factor(z, mu, c2, q):
    """Power multiplier of zeta at 4D wavenumber K, z = K/K_V, relative to 5D GR.

    (z/(z + mu))^2: the 6D propagator, mu = m/K_V. r^(2 s(z)): the tensor-structure change,
    unscreened (s = 1) at small K, screened (s = 0) at large K, s = 1/(1 + z^q).
    """
    s = 1.0 / (1.0 + z**q)
    return (z / (z + mu)) ** 2 * spatial_ratio(c2) ** (2.0 * s)


def part_a():
    print("Part A. Tensor structure, massive/massless, for 0 <= c^2 <= 1/4:")
    print(f"  {'c^2':>5} {'zeta (spatial)':>15} {'Newtonian':>10}")
    for c2 in (0.0, 0.1, 0.2, 0.25):
        print(f"  {c2:5.2f} {spatial_ratio(c2):15.4f} {newtonian_ratio(c2):10.4f}")
    print("  zeta is never boosted; the Newtonian potential is (except for radiation).")

    worst = np.inf
    for c2 in (0.0, 0.25):
        for mu in (0.0, 1e-3, 1e-1, 1.0, 10.0):
            for q in (0.5, 1.5, 3.0):
                if mu == 0.0 and c2 == 0.25:
                    continue  # factor is identically 1
                F = lambda z, mu=mu, c2=c2, q=q: cascade_factor(z, mu, c2, q)
                for y in np.geomspace(1e-3, 1e3, 25):
                    worst = min(worst, derivs(F, y)[0])
    print(f"  smallest n_s - 1 over c^2 in {{0, 1/4}}, mu in [0, 10], q in [0.5, 3],"
          f" y in [1e-3, 1e3]: {worst:.3e} (> 0: blue everywhere)")
    F = lambda z: cascade_factor(z, 1.0, 0.25, 1.0)
    print(f"  radiation atmosphere, mu = 1: n_s - 1 at y = 0.1, 1, 10:",
          ", ".join(f"{derivs(F, y)[0]:.3f}" for y in (0.1, 1.0, 10.0)))


# --- Part B: what an IR boost would have to look like ----------------------------------------

def boost(z, B, q):
    """Power multiplier exp(B / (1 + z^q)): a boost of ln P by B that switches on below K_V."""
    return np.exp(B / (1.0 + z**q))


def part_b():
    bmax = 2.0 * np.log(newtonian_ratio(0.0))
    print("\nPart B. Counterfactual: zeta boosted like the Newtonian potential of dust,")
    print(f"  F = exp(B / (1 + (K/K_V)^q)), B <= 2 ln(9/8) = {bmax:.4f}.")
    print("  Unprojected: n_s - 1 = -B q u/(1+u)^2, alpha_s = -B q^2 u(1-u)/(1+u)^3,"
          " u = (k/K_V)^q;")
    print("  on either tail alpha_s/(n_s - 1) -> -q or +q, and |n_s - 1| <= B q/4.")
    print(f"  {'q':>5} {'B for n_s':>9} {'passing k_V range (1/Mpc)':>28} {'best chi2':>10}")
    for q in (0.5, 0.75, 1.0, 1.5, 2.0, 3.0):
        best, kv = np.inf, []
        for B in np.linspace(0.01, bmax, 24):
            F = lambda z, B=B, q=q: boost(z, B, q)
            for y in np.geomspace(0.05, 20.0, 41):
                n1, a, b = derivs(F, y)
                c = ((1 + n1 - NS) / SIG_NS) ** 2 + ((a - ALPHA) / SIG_ALPHA) ** 2
                if c >= CHI2_2SIGMA_2DOF:
                    continue
                lnp = lnI(F, y * K_HI / K_PIV) - lnI(F, y * K_LO / K_PIV)
                if abs(lnp - LNP_PL) > 2 * SIG_LNP or abs(b - BETA) > 2 * SIG_BETA:
                    continue
                best = min(best, c)
                kv.append((K_PIV / y, B))
        need = 4.0 * (1.0 - NS) / q
        if kv:
            ks = [p[0] for p in kv]
            rng = f"[{min(ks):.3f}, {max(ks):.3f}]"
        else:
            rng = "none"
        print(f"  {q:5.2f} {need:9.3f} {rng:>28} {best:10.2f}")
    print("  (B for n_s: the least B that reaches n_s = 0.9649 anywhere. The projected tilt is an")
    print("  average of d ln F/d ln K, so |n_s - 1| <= B q/4 holds on the brane too.)")


def main():
    part_a()
    part_b()


if __name__ == "__main__":
    main()
