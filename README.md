## QuickCheck models for `aeternity/epoch`

### Suggested workflow
 * Check out this repo into e.g. `epoch/eqc`
 * Start a shell using rebar3 (from `epoch/`): `./rebar3 as test shell --apps=""`
 * Move into the directory containing the models you would like to run, e.g.: `1> cd("eqc/aeutils_eqc").`
 * Compile the model, e.g.: `2> c(aeu_rlp_eqc).`
 * Run the tests, e.g.: `3> eqc:quickcheck(aeu_rlp_eqc:prop_roundtrip()).`
