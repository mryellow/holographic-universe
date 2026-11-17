#!/usr/bin/env python3
"""Golden values (ROADMAP M8.4): check the numerical code against numbers proved in Lean.

Each expected value below is an exact theorem in `HolographicUniverse/Golden.lean` (or the file
named next to it). If one of these tests fails, the Python code and the Lean formulas disagree.

Usage (from phenomenology/):  uv run python tests/test_golden.py     (or: uv run pytest tests)
"""
import importlib.util
import math
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent.parent


def _load(rel):
    spec = importlib.util.spec_from_file_location(Path(rel).stem, HERE / rel)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


jeans = _load("p1_jeans/jeans_tilt.py")
cascade = _load("p2_cascade/cascade_tilt.py")


def dlog(f, x, h=1e-4):
    """d ln f / d ln x, by a central difference."""
    return (np.log(f(x * np.exp(h))) - np.log(f(x * np.exp(-h)))) / (2 * h)


def ddlog(f, x, h=1e-3):
    """d² ln f / d ln x², by a central difference."""
    return (np.log(f(x * np.exp(h))) - 2 * np.log(f(x)) + np.log(f(x * np.exp(-h)))) / h**2


def close(a, b, tol):
    assert abs(a - b) <= tol, f"{a} != {b} (tol {tol})"


# --- P1, Jeans (Jeans.lean, Golden.lean) -------------------------------------------------------

def test_jeans_bulk_ratio():
    """runningIndex_jeans: alpha_s / (n_s - 1) = 1 + 1/(1 - y^2) = 41/16 at y = 3/5."""
    close(jeans.bulk_ratio(0.6), 41 / 16, 1e-14)


def test_jeans_unprojected():
    """golden_jeans_tilt, golden_jeans_running: tau = 1, y = 3/5 -> -9/10 and -369/160."""
    F = lambda y: np.exp(2 * 1.0 * np.sqrt(1 - y * y))
    close(dlog(F, 0.6), -9 / 10, 1e-7)
    close(ddlog(F, 0.6), -369 / 160, 1e-5)


def test_jeans_growth_matches_large_tau_form():
    """The script's exact growth cosh^2(tau s) has the same log-slope as e^{2 tau s} for large tau."""
    tau = 30.0
    slope = jeans.zgrowth(0.6, tau) / jeans.growth(0.6, tau)
    close(slope, -2 * tau * 0.36 / 0.8, 1e-10)


def test_jeans_projected_above():
    """jeansProjected_of_one_le, golden_jeansProjected: I(6/5) = pi/2 and n_s = 1, any tau."""
    for tau in (0.2, 1.0, 5.0):
        close(jeans._integrate(lambda z: jeans.growth(z, tau), 1.2), math.pi / 2, 1e-10)
        close(jeans.tilt(1.2, tau), 0.0, 1e-14)


def test_jeans_budget():
    """tendsto_jeansProjected_zero: I(y) -> (pi/2) cosh^2 tau as y -> 0 (the result 3 budget)."""
    for tau in (0.188, 1.0):
        close(jeans._integrate(lambda z: jeans.growth(z, tau), 1e-4), math.pi / 2 * math.cosh(tau) ** 2, 1e-6)


# --- P2, cascade and boost (Cascade.lean, Boost.lean, Golden.lean) -----------------------------

def test_cascade_coefficients():
    """coeff_dust: 3/4 and 9/8 for dust; spatialCoeff_radiation: no change for radiation."""
    close(cascade.spatial_ratio(0.0), 3 / 4, 1e-15)
    close(cascade.newtonian_ratio(0.0), 9 / 8, 1e-15)
    close(cascade.spatial_ratio(0.25), 1.0, 1e-15)


def test_projection_without_growth():
    """integral_univ_inv_one_add_sq_sq: I = pi/2 for F = 1."""
    close(cascade.project(lambda z: 1.0, 0.7), math.pi / 2, 1e-10)


def test_boost_centre():
    """golden_boost_centre_tilt, golden_boost_centre_running: B = 1, q = 2, u = 1."""
    F = lambda z: cascade.boost(z, 1.0, 2.0)
    close(dlog(F, 1.0), -1 / 2, 1e-7)
    close(ddlog(F, 1.0), 0.0, 1e-5)


def test_boost_tail():
    """golden_boost_tilt, golden_boost_running: B = 1, q = 1, u = 2."""
    F = lambda z: cascade.boost(z, 1.0, 1.0)
    close(dlog(F, 2.0), -2 / 9, 1e-7)
    close(ddlog(F, 2.0), 2 / 27, 1e-5)


def test_boost_projected_bound():
    """abs_boostTilt_le: the brane tilt is a weighted average, so |n_s - 1| <= |B| q / 4."""
    for B, q in ((0.2, 1.0), (0.24, 1.5), (0.1, 3.0)):
        for y in (0.1, 0.5, 1.0, 2.0):
            n1, _, _ = cascade.derivs(lambda z: cascade.boost(z, B, q), y)
            assert abs(n1) <= B * q / 4 + 1e-6, (B, q, y, n1)


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for t in tests:
        t()
        print(f"ok  {t.__name__}")
    print(f"{len(tests)} passed")
