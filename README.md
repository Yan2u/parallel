### An Axiomatic Proof Technique for Parallel Programs I*

#### File Structure

- `Tactics.v`: Some basic tactics;
- `Semantics.v`: Small-step definition of an extented `imp` language to support alternative execution;
- `State.v`: Super simple memory model of the language from "Software Foundation";
- `VarSet.v`: Definitions to create a set of variables. This is to model and prove theorem "auxiliary variables transformation";
- `Proofs.v`: Specific proofs in the essay.

#### Current Progress

**Finished**

- Proofs (4.1), (4.2) (findpos);

**TODOs**

- Proof of `hoare_while`;
- Proof of `auxiliary_variables_transformation`;
- Proofs in the chapters left.

#### Usage

- First build

    `make clean; coq_makefile -f _CoqProject -o Makefile; make `

    this will not compile `Proofs.v` because it is not finished.

- Clean up and rebuild

    Add `make clean` before the commands above.