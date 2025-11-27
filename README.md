= Generic RGSep =

This repository contains an implemetation of a Generic RGSep and a proof of its soundness.

== Theories ==

* Util.thy provides many useful lemmas
* SepLogic.thy provides a typeclass hierarchy for separation algebras, and separation logic built on them
* SepAlgInstances.thy provides several common separation algebra instances
* MoreSepAlgInstances.thy provides more separation algebra instances
* Lang.thy provides the basic definitions of the programming language
* RGLogic.thy provides the RGSep rules for the language
* Soundness.thy provides the semantics for the language, and a proof of the soundness of the logic

* Security.thy develops an information-flow security logic based on GenRGSep

== Building ==

This theory has been tested with Isabelle2025, and does not require any external libaries.

Isabelle2025 can be obtained from: <https://isabelle.in.tum.de/>.
