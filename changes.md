2024-11-06:
* Changed + to do a tau move.
* Changed DO semantics to be directly defined using `~opstep`.
* Removed mu recursion remnants.

2024-10-30:
* I had to change the enabledness condition in do-od!!! The previous statement was wrong, because we really want `stuck`, and loops can never be 'stuck' because if the interior gets stuck the loop just exits.
* I had to add a frame closure condition to atomic rules, because, after separating the precondition from the relational postcondition / update relation, it is now necessary to constrain the domain of this update, which leads to a mismatch when you know `p s`, but have to evaulate `aq (s + f) (s' + f)`.
* `safe_atom'` has been generalised, but in a way, I think, that makes the rule nicer to use than the previous version, without sacrificing the power of the previous rule.
* The iteration rule is a bit more troublesome. Ideally we would prove it with the weakest possible assumption `{ wssa r i } c { sswa r i }`, but this does not seem to work with the safety proof.

2024-10-28:
* I reworked some of the rgsat rules to make weakening easier to prove admissible. We still can't prove strong weakening is admissible, due to some technical issues.
* I changed atomics to take a precondition and relational postcondition, instead of returning a crash value. This makes reasoning with them slightly nicer.
* I changed rgsat to only use a standard postcondition. You show the abscence of a crash by demonstrating a proof exists.

