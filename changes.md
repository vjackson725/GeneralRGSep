
2024-10-28:
* I reworked some of the rgsat rules to make weakening easier to prove admissible. We still can't prove strong weakening is admissible, due to some technical issues.
* I changed atomics to take a precondition and relational postcondition, instead of returning a crash value. This makes reasoning with them slightly nicer.
* I changed rgsat to only use a standard postcondition. You show the abscence of a crash by demonstrating a proof exists.

