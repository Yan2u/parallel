#### 2025-03-05

- We cannot make inductions on the structure of statement `WHILE`, because when it is reduced one step forward, it's structure changes to `TEST`, which cannot fit the prop;

- We may use **invariants** before and after reduction to prove that: **if `P a -> R a b -> P b`**, `P` is `X -> Prop`, `R` is the reduction relation, and **then forall `c` where `multi R a c`, we have `P c`**.

- Unable to find such invariants to fit my `iter_count` props.

#### 2025-03-06

Notes on proof of `hoare_while`;

- Find that when I use `Induction`, a likely reversed invariant infer `P b -> R a b -> P a` will automatically be constructed via the induction system;

- By using `while_succ` and `is_seq`, I can:

    + Limit the structure of the statements in the progress to `WHILE`, `TEST _ THEN (_ ;; WHILE) ELSE SKIP FI`, `_ ;; _` and `SKIP`;

    + Deal with different structure of statements above by `is_seq`, and the point is to deal with **transitions between two different structures** (E.g. `TEST -> _ ;; _`)

    + Put `exists n, iter_count ...` in the induction hypothesis, but not to prove it directly;

- No need to use `P a -> R a b -> P b` in `com_while_count`;

- Main proof chain: `step_infer` → `multi_infer` → `com_while_succ` → `com_while_count_pre` → `com_while_count` → `hoare_while`.