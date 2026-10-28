= Generic RGSep =

This repository contains an implemetation of a Generic RGSep and a proof of its soundness.

== Theories ==

In the main folder are the theories for GenRGSep
* Util.thy provides many useful lemmas
* SepLogic.thy provides a typeclass hierarchy for separation algebras, and separation logic built on them
* SepAlgInstances.thy provides several common separation algebra instances
* MoreSepAlgInstances.thy provides more separation algebra instances
* Lang.thy provides the basic definitions of the programming language
* RGLogic.thy provides the RGSep rules for the language
* Soundness.thy provides the semantics for the language, and a proof of the soundness of the logic

In `/models`, two more models of state are given
* Failure.thy shows how to encode failure into the local state. This allows for the assertion command.
* Heap.thy shows how to encode a generic heap model. This allows for heap update, read, allocation, and free.

In `/sec`
* SecLogic.thy gives the basic relational logic for information flow security;
  in particular lifting and agreement.
* SecLang.thy gives the basic security commands, such as output and declassify.
* Security.thy develops an information-flow security logic based on GenRGSep

This theory has been tested with Isabelle/HOL 2025, and does not require
any external libaries. Isabelle/HOL can be obtained from
<https://isabelle.in.tum.de/>.

== Building ==

This theory has been tested with Isabelle2025, and does not require any external libaries.

Isabelle2025 can be obtained from: <https://isabelle.in.tum.de/>.
