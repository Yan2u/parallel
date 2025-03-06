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

- ✅: Proof of `hoare_while`;
- Proof of `auxiliary_variables_transformation`;
- Proofs in the chapters left.

#### Usage

- First build

    `make clean; coq_makefile -f _CoqProject -o Makefile; make `

    this will not compile `Proofs.v` because it is not finished.

- Clean up and rebuild

    Add `make clean` before the commands above.

#### 2025-03-05

- Proved `hoare_while` using defined `iter_count`, which describes that in n loops, the condition `b` evals to `false` after the last loop and evals to `true` before the last loop.

- **Unable to prove that**: if a `WHILE` statement at state `st` is reduced to `SKIP` at state `st'`, then there exists `n`, s.t. `iter_count b c n st st'`.

#### 2025-03-06

- Finish whole proof chain of `hoare_while`, using `iter_count` and a lemma `com_hoare_count_pre`;

- Created Notes.md and move **thoughts** in.