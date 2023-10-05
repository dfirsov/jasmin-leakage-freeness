## Requirements

```
EASYCRYPT_REVISION =  a214a56
JASMIN_VERSION     =  2023.06.1
ALT-ERGO           >= v2.5.1
CVC4               >= 1.8
Z3                 >= 4.8.7
```

The EasyCrypt config (`~/.config/easycrypt/easycrypt.conf`) must contain Jasmin `eclib` library loadpath: `idirs=Jasmin:YOUR_LOCAL_PATH/code/proof/eclib/`.

## Makefile
* `make check_all` runs the EasyCrypt proof-checker on the entire development (requires CVC4, Alt-Ergo, and Z3 SMT solvers).
* `make compile_and_run` compiles and runs rejections sampling algorithm (Jasmin implementation in `src/bn_rsample.jazz`; linked together by C-wrapper `src/example/example.c`).

## Contents

### `src/`
* `constants.jazz` defines Jasmin's global variable `bn_glob_p` to be equal to a 2048-bit safe prime from RFC 352 which is used for testing.
* `bn_rsample.jazz` implements uniform sampling from `[0..bn_glob_p-1]` interval.
* `bn_rsample.h` C-interface of external calls for the uniform sampling entry points.
* `example/example.c` C-wrapper which links the rejection sampling function with systemcall providers.
* `example/syscalls/` (random and pseudo-random) implementation of Jasmin's `#randombytes` systemcall.

### `proof/`
* `LeakageFreeness_Analysis.ec` - analysis of leakage-freeness definitions (see the paper).
* `auxiliary_lemmas/`
   - `AuxLemmas.ec` auxiliary lemmas.
   - `SurjFromInj.ec` derives surjectivity from injectivity of functions of finite set of same cardinality.
   - `ArrayFiniteness.ec` derives finiteness of `ArrayN` and `WArrayN`  types.
* `big_num_ops/`:
   - `BigNum_proofs.ec` proof of correctness for (simple) Jasmin procedures on big-nums needed for `bn_rsample`.
   - `BigNum_spec.ec` parameters and (abstract + semi-abstract) specification of operations on big-nums.
   - `BigNum_instances.ec` instantiation of big-nums for a particular nlimbs (= 32).
   - `leakage_freeness/` proofs of CT of operations on big-nums.
* `rejection_sampling/`
  - `RejectionSamplingModule.eca` abstract rejection sampling algorithm in EasyCrypt.
  - `RejectionSamplingProperties.eca` main properties of abstract EasyCrypt's rejection sampling algorithm.  
  - `UniformSampling_Concrete.ec` proof that Jasmin's function `bn_rsample` implements rejection sampling correctly.
  - `leakage_freeness/` proof of `LFdef(bn_rsample)`.
  - `leakage_freeness_prhl/` pRHL proof of leakage-freeness of rejection sampling.
* `jasmin_extracts/` folder which contains EasyCrypt code extracted by Jasmin compiler.
* `eclib/` Jasmin's library for EasyCrypt.
