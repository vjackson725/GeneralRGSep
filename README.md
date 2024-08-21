= Generic RGSep =

This repository contains an implementation of a Generic RGSep and a proof of its soundness.

== Theories ==

* Util.thy provides many theories
* Seplogic.thy provides a typeclass hierarchy for separation algebras, and separation logic built on them
* SepAlgInstances.thy provides several common separation algebra instances
* Lang.thy provides the definition of the language
* RGLogic.thy provides the RGSep rules for the language
* Soundness.thy provides a small-step semantics for the language, and a proof of the soundness of the logic

== Building ==

This theory has been tested with Isabelle2023, and does not require any specialised libaries.

Isabelle2023 can be obtained from: <https://isabelle.in.tum.de/>.

The primary theorem is `soundness` in `Soundness.thy`.
