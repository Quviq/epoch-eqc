## QuickCheck models for `aeternity/epoch`

### Suggested workflow
 * Check out this repo into e.g. `epoch/eqc`
 * Start a shell using rebar3 (from `epoch/`): `./rebar3 as test shell --apps=""`
 * Move into the directory containing the models you would like to run, e.g.: `1> cd("eqc/aeutils_eqc").`
 * Compile the model, e.g.: `2> c(aeu_mp_trees_eqc).`
 * Run the tests, e.g.: `3> eqc:quickcheck(aeu_mp_trees_eqc:prop_insert_delete()).`
