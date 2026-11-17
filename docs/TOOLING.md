# Tooling

This document tells you how to install the tools for this project. The project has two parts:

- **Lean library** (`HolographicUniverse/`): the formal proofs. It needs Lean 4 and Mathlib.
- **Phenomenology** (`phenomenology/`): the numerical code for the tests in
  [`TESTABILITY.md`](TESTABILITY.md). It needs Python, CAMB, CLASS, Cobaya and, for model
  comparison, PolyChord.

You can install the Lean part without the Python part, and the Python part without the Lean part.

The commands were tested on Debian 13 (glibc 2.41, GCC 14.2). Other Linux systems may need
different package names.

## 1. System packages

1. Install the compilers and tools:
   ```bash
   sudo apt install curl git gcc g++ make
   ```
2. Install a Fortran compiler and MPI. Do this step only if you need PolyChord (section 4):
   ```bash
   sudo apt install gfortran libopenmpi-dev
   ```

## 2. Lean

1. Install elan, the Lean version manager:
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
   ```
2. Load the elan path into your shell. A new shell does this automatically.
   ```bash
   source "$HOME/.elan/env"
   ```
3. Go to the repository root:
   ```bash
   cd holographic-universe
   ```
4. Download the prebuilt Mathlib files. elan reads `lean-toolchain` and installs the correct
   Lean version on the first run.
   ```bash
   lake exe cache get
   ```
5. Build the project:
   ```bash
   lake build
   ```

## 3. Python environment

The environment uses [uv](https://docs.astral.sh/uv/). `phenomenology/pyproject.toml` lists the
packages, and `phenomenology/uv.lock` sets their exact versions.

uv must use its own Python build, not the system Python. The system Python on Debian has no
development headers, so `classy` does not compile with it. The setting
`python-preference = "only-managed"` in `pyproject.toml` makes uv use its own Python.

1. Install uv if `uv --version` fails:
   ```bash
   curl -LsSf https://astral.sh/uv/install.sh | sh
   ```
2. Go to the phenomenology directory:
   ```bash
   cd phenomenology
   ```
3. Create the environment and install the packages. uv downloads Python 3.13 if necessary.
   `classy` compiles from source, so this step can take several minutes.
   ```bash
   uv sync
   ```
4. Run a short test. CAMB and CLASS must each print an age of approximately 13.7 Gyr.
   ```bash
   uv run python -c "
   import camb, classy
   r = camb.get_results(camb.set_params(H0=67.5, ombh2=0.022, omch2=0.122, As=2e-9, ns=0.965))
   print('CAMB age', round(r.physical_time(0), 2), 'Gyr')
   c = classy.Class(); c.set({'output': 'tCl'}); c.compute()
   print('CLASS age', round(c.age(), 2), 'Gyr')
   "
   ```

To run code in the environment, use `uv run python <script>` from `phenomenology/`.

## 4. PolyChord (optional)

PolyChord is a nested sampler. It calculates the Bayesian evidence, which you need to compare
the model with ΛCDM. You do not need it to fit parameters, because Cobaya's default MCMC sampler
does that.

PolyChordLite 1.20.1 does not build on this system without two changes to its source:

- **`HOME` is not set.** `setup.py` runs `make` with only `PATH` in the environment. Open MPI's
  `mpifort` stops with "Unable to get the user home directory" when `HOME` is not set.
- **Executable stack.** gfortran puts trampolines on the stack for two files (`interfaces.F90`,
  `maximiser.F90`). This marks `libchord.so` as needing an executable stack. glibc 2.41 and
  later do not load such a library. The GCC 14 flag `-ftrampoline-impl=heap` moves the
  trampolines to the heap. Do not only clear the flag with `patchelf` or `execstack`: the
  library could then crash when it calls the trampolines.

Do sections 1 and 3 first. Then do these steps in `phenomenology/`:

1. Download PolyChord. The command stops with a compile error. This is expected, because the
   download has not been patched yet.
   ```bash
   uv run cobaya-install polychord --packages-path ./packages
   ```
2. Go to the downloaded source:
   ```bash
   cd packages/code/PolyChordLite
   ```
3. Make `setup.py` pass `HOME` to `make`:
   ```bash
   sed -i 's/^        env\["PATH"\] = os.environ\["PATH"\]$/        env["PATH"] = os.environ["PATH"]\n        env["HOME"] = os.environ.get("HOME", os.path.expanduser("~"))/' setup.py
   ```
4. Add the heap-trampoline flag to the Fortran flags:
   ```bash
   sed -i 's/-fno-stack-arrays /-fno-stack-arrays -ftrampoline-impl=heap /' Makefile_gnu
   ```
5. Remove the output of the failed build:
   ```bash
   rm -rf build lib/libchord.so src/polychord/*.o src/polychord/*.mod pypolychord/lib
   ```
6. Build PolyChord:
   ```bash
   uv run --project ../../.. python setup.py build
   ```
7. Make sure that the library does not ask for an executable stack. The output must show `RW`,
   not `RWE`.
   ```bash
   readelf -lW lib/libchord.so | grep GNU_STACK
   ```
8. Go back to `phenomenology/` and run the installer again. It must report
   "All requested components' dependencies correctly installed".
   ```bash
   cd ../../..
   uv run cobaya-install polychord --packages-path ./packages
   ```

`cobaya-install --upgrade` downloads the source again and removes these changes. If you upgrade,
do steps 2 to 8 again, unless the new release fixes the two problems.

`phenomenology/packages/` is in `.gitignore`, so the downloaded code stays out of the
repository.

### Test with a known answer

This test samples a 2D unit Gaussian with a uniform prior on [−5, 5]². The exact evidence is
log Z = −ln 100 ≈ −4.605. With 200 live points, a result within approximately 0.1 of this value
is normal. One test run gave −4.52 ± 0.05.

```bash
uv run python -c "
import numpy as np
from cobaya.run import run
info = {
    'likelihood': {'g': lambda x, y: -0.5*(x**2 + y**2) - np.log(2*np.pi)},
    'params': {'x': {'prior': {'min': -5, 'max': 5}}, 'y': {'prior': {'min': -5, 'max': 5}}},
    'sampler': {'polychord': {'nlive': 200, 'precision_criterion': 0.01}},
    'packages_path': './packages', 'output': '/tmp/polychord_test/gauss', 'force': True,
}
_, s = run(info)
print('logZ =', s.products()['logZ'], '+/-', s.products()['logZstd'], '(exact -4.605)')
"
```

## 5. Likelihood data (later)

The Planck, ACT and DESI likelihoods need several GB of data. Download them only when a pathway
in [`TESTABILITY.md`](TESTABILITY.md) needs them. Use `cobaya-install` with the likelihood
name, for example:

```bash
uv run cobaya-install planck_2018_highl_plik.TTTEEE --packages-path ./packages
```
