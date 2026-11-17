#!/usr/bin/env python3
"""P1: tilt and running from a residual Jeans instability of the bulk atmosphere.

See README.md in this directory for the derivation. In short: the 4D (bulk) density contrast
of the thermal atmosphere grows as

    F(z) = cosh^2(tau * sqrt(1 - z^2))   for z = K/K_J < 1,
    F(z) = 1                             for z >= 1 (the mode oscillates),

with tau = Gamma_0 * Delta t the number of e-folds of growth of the longest modes. The brane
sees the 4D spectrum through the integral over the fourth momentum component in Eq. (48):

    Delta^2_zeta(k)  propto  I(y) = int dx (1 + x^2)^-2 F(y sqrt(1 + x^2)),   y = k / K_J,

where K_J is the physical Jeans wavenumber at a_b, in comoving units. Then

    n_s - 1 = d ln I / d ln y,   alpha_s = d n_s / d ln y.

The thermal factor M(k sqrt(1+x^2)/(a_b T_b)) is left out. M7.3 proves that it is blue at
every scale; near the Jeans scale it adds at most ~1e-4 to n_s - 1 (see README.md).

Usage:  uv run python p1_jeans/jeans_tilt.py      (from phenomenology/)
"""
import numpy as np
from scipy.integrate import quad

# Planck 2018. n_s: TT,TE,EE+lowE+lensing (ObsData.planck2018 in the Lean library).
# alpha_s: Planck 2018 X (arXiv:1807.06211), LCDM + running, same data, 68% CL.
NS, SIG_NS = 0.9649, 0.0042
ALPHA, SIG_ALPHA = -0.0045, 0.0067


def growth(z, tau):
    """Power growth factor F(z) of a 4D mode with z = K/K_J."""
    if z >= 1.0:
        return 1.0
    return np.cosh(tau * np.sqrt(1.0 - z * z)) ** 2


def zgrowth(z, tau):
    """z F'(z): the derivative of F with respect to ln K."""
    if z >= 1.0:
        return 0.0
    s = np.sqrt(1.0 - z * z)
    # F' = 2 cosh sinh * tau * (-z/s) = -tau z sinh(2 tau s)/s; sinh(2 tau s)/s -> 2 tau at s=0.
    ratio = np.sinh(2.0 * tau * s) / s if s > 1e-8 else 2.0 * tau
    return -tau * z * z * ratio


def _integrate(f, y):
    """int_{-inf}^{inf} (1 + x^2)^-2 f(y sqrt(1 + x^2)) dx, split at the Jeans cut z = 1."""
    w = lambda x: (1.0 + x * x) ** -2 * f(y * np.sqrt(1.0 + x * x))
    if y >= 1.0:
        return 2.0 * quad(w, 0.0, np.inf, limit=400)[0]
    xc = np.sqrt(1.0 / (y * y) - 1.0)
    inner = quad(w, 0.0, xc, limit=400, epsabs=0.0, epsrel=1e-12)[0]
    outer = quad(w, xc, np.inf, limit=400, epsabs=0.0, epsrel=1e-12)[0]
    return 2.0 * (inner + outer)


def tilt(y, tau):
    """n_s - 1 = d ln I / d ln y on the brane."""
    I = _integrate(lambda z: growth(z, tau), y)
    J = _integrate(lambda z: zgrowth(z, tau), y)
    return J / I


def running(y, tau, h=1e-4):
    """alpha_s = d n_s / d ln y, by a central difference in ln y."""
    return (tilt(y * np.exp(h), tau) - tilt(y * np.exp(-h), tau)) / (2.0 * h)


def bulk_ratio(y):
    """alpha/(n_s - 1) for the unprojected 4D spectrum with F = exp(2 tau s): 1 + 1/(1 - y^2)."""
    return 1.0 + 1.0 / (1.0 - y * y)


def chi2(ns_minus_1, alpha):
    return ((1.0 + ns_minus_1 - NS) / SIG_NS) ** 2 + ((alpha - ALPHA) / SIG_ALPHA) ** 2


def running2(y, tau, h=1e-3):
    """beta_s = d^2 n_s / d ln y^2, by a central difference in ln y."""
    return (tilt(y * np.exp(h), tau) - 2.0 * tilt(y, tau) + tilt(y * np.exp(-h), tau)) / h**2


def drop(y1, y2, tau):
    """ln I(y2) - ln I(y1) = int (n_s - 1) d ln k between the two scales."""
    g = lambda z: growth(z, tau)
    return np.log(_integrate(g, y2)) - np.log(_integrate(g, y1))


# The best-measured range of the primordial spectrum (Planck 2018 X, Sec. 6), in 1/Mpc.
K_LO, K_HI, K_PIV = 0.008, 0.1, 0.05
CHI2_2SIGMA_2DOF = 6.18


def scan():
    """Grid over (tau, y_pivot). Returns the best point and the points that pass the joint
    (n_s, alpha_s) test at 2 sigma for 2 parameters."""
    taus = np.geomspace(1e-2, 30.0, 61)
    ys = np.concatenate([np.geomspace(1e-3, 0.5, 50), np.linspace(0.5, 0.999, 60)[1:]])
    best, passing, ns_ok = (np.inf, None), [], False
    for tau in taus:
        for y in ys:
            n1, a = tilt(y, tau), running(y, tau)
            ns_ok |= abs(1.0 + n1 - NS) < 2.0 * SIG_NS
            c = chi2(n1, a)
            if c < best[0]:
                best = (c, (tau, y, n1, a))
            if c < CHI2_2SIGMA_2DOF:
                passing.append((tau, y, n1, a, c))
    return best, passing, ns_ok


def main():
    print("Unprojected check: alpha/(n_s-1) = 1 + 1/(1-y^2) >= 2 for y in (0, 1).")
    for y in (0.01, 0.3, 0.7):
        print(f"  y={y:5.2f}: bulk ratio {bulk_ratio(y):.4f}")

    print("\nProjected (brane) spectrum, samples:")
    print(f"  {'tau':>6} {'y':>7} {'n_s-1':>11} {'alpha_s':>11} {'alpha/(n_s-1)':>14}")
    for tau in (0.1, 1.0, 5.0):
        for y in (0.05, 0.2, 0.5, 0.8):
            n1, a = tilt(y, tau), running(y, tau)
            print(f"  {tau:6.2f} {y:7.3f} {n1:11.4e} {a:11.4e} {a / n1:14.4f}")
    print("  above the Jeans scale, y = 1.2, tau = 1: n_s - 1 =", tilt(1.2, 1.0))
    print("Limit tau, y -> 0 (ratio should approach 2):",
          f"{running(1e-2, 1e-2) / tilt(1e-2, 1e-2):.5f}")

    # Regime 1: pivot well inside the unstable range (y <= 0.3): alpha ~ 2(n_s - 1).
    print("\nRegime y <= 0.3: tau chosen so that n_s = 0.9649 at the pivot")
    for yp in (0.01, 0.05, 0.1, 0.2, 0.3):
        lo, hi = 1e-3, 200.0
        for _ in range(100):  # tilt is monotone in tau at fixed y
            mid = np.sqrt(lo * hi)
            if tilt(yp, mid) > NS - 1.0:
                lo = mid
            else:
                hi = mid
        tau = np.sqrt(lo * hi)
        a = running(yp, tau)
        print(f"  y={yp:5.2f}: tau={tau:7.3f}, alpha_s={a:8.4f}, "
              f"{abs(a - ALPHA) / SIG_ALPHA:5.1f} sigma from Planck")

    best, passing, ns_ok = scan()
    c, (tau, y, n1, a) = best
    print("\nScan over tau in [0.01, 30], y in [1e-3, 0.999]:")
    print(f"  n_s alone within 2 sigma somewhere: {ns_ok}")
    print(f"  best joint point: tau={tau:.3g}, y={y:.3g}, n_s={1 + n1:.4f}, "
          f"alpha_s={a:.4f}, chi^2={c:.2f}")
    print(f"  points passing the joint test at 2 sigma: {len(passing)}")
    if passing:
        ys_ = [p[1] for p in passing]
        ts_ = [p[0] for p in passing]
        print(f"  their y_pivot range: [{min(ys_):.3f}, {max(ys_):.3f}]; "
              f"tau range: [{min(ts_):.3f}, {max(ts_):.3f}]")
        # Shape across the measured range for each passing point.
        pl = (NS - 1.0) * np.log(K_HI / K_LO)
        drops = [drop(p[1] * K_LO / K_PIV, p[1] * K_HI / K_PIV, p[0]) for p in passing]
        print(f"  ln P(0.1)/P(0.008): Planck power law {pl:.4f} +- "
              f"{SIG_NS * np.log(K_HI / K_LO):.4f}; passing points "
              f"[{min(drops):.4f}, {max(drops):.4f}]; total possible drop 2 ln cosh(tau) <= "
              f"{2 * np.log(np.cosh(max(p[0] for p in passing))):.4f}")
        print(f"  k_J = k_pivot / y_pivot in [{K_PIV / max(ys_):.4f}, {K_PIV / min(ys_):.4f}]/Mpc;"
              " n_s = 1 exactly for k >= k_J")
        b = [running2(p[1], p[0]) for p in passing]
        print(f"  beta_s = d^2 n_s/d ln k^2 at the pivot: [{min(b):.3f}, {max(b):.3f}] "
              "(Planck 2018 X with beta free: 0.022 +- 0.012)")
        print("  n_s(k) at the best point:")
        for k in (0.002, 0.01, 0.03, 0.05, 0.06, 0.1, 0.2):
            print(f"    k={k:6.3f}/Mpc: n_s = {1 + tilt(y * k / K_PIV, tau):.4f}")


if __name__ == "__main__":
    main()
