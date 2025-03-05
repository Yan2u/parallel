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

#### 2025-03-05

- Proved `hoare_while` using defined `iter_count`, which describes that in n loops, the condition `b` evals to `false` after the last loop and evals to `true` before the last loop.

- **Unable to prove that**: if a `WHILE` statement at state `st` is reduced to `SKIP` at state `st'`, then there exists `n`, s.t. `iter_count b c n st st'`.

- Thoughts:

    + We cannot make inductions on the structure of statement `WHILE`, because when it is reduced one step forward, it's structure changes to `TEST`, which cannot fit the prop;

    + We may use **invariants** before and after reduction to prove that: **if `P a -> R a b -> P b`**, `P` is `X -> Prop`, `R` is the reduction relation, and **then forall `c` where `multi R a c`, we have `P c`**.

    + Unable to find such invariants to fit my `iter_count` props.