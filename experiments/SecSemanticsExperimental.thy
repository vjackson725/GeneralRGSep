theory SecSemanticsExperimental
  imports "../sec/Semantics"
begin

definition quasirefl_cl (\<open>\<^bold>\<box>\<close>) where
  \<open>quasirefl_cl p \<equiv> \<lambda>(x,y). p (x,y) \<and> p (x,x) \<and> p (y,y)\<close>

lemma quasirefl_cl_mono:
  \<open>p \<le> q \<Longrightarrow> \<^bold>\<box>p \<le> \<^bold>\<box>q\<close>
  unfolding quasirefl_cl_def
  by blast

lemma
  \<open>\<^bold>\<box>p = p \<longleftrightarrow> (\<forall>x y. p (x,y) \<longrightarrow> p (x,x) \<and> p (y,y))\<close>
  unfolding quasirefl_cl_def
  by (force simp add: fun_eq_iff)

(* 
Let c be a simple program that operates on a single state and 
let \<oo> be  a function describing the observations the attacker can make on a given state,
the function (liftC \<oo> c) turns the program c into one that operates on a pair of states and that crashes
when run on states that are distingishable through  \<oo>. This in turn, which can be  used for info flow reasoning.



the safe judgement provides the same amount of information as a programming language semantics that 
is a tree T of all possible executions that can happen, as well as a proof that if the precondition and 
the relies, then for all possible executions in the tree
   (1) they don't fail and
   (2) the obey the guarantees and the postcondition
   (3) the frame condition is preserved


define function f ( c, n, p, r) = trees T

prove
theorems 
safe_imp_no_crash:"safe  c, n, p, r, q,g \<longrightarrow> 
  (1) the program f ( c, n, p, r) does not crash,
  (2) the program  obey the guarantees and the postcondition
  (3) the frame condition is preserved


definition noninterference is: given a pair of states s1 and s2, indistinguishable by \<oo>,
no execution of the program on s1 and s2 respectively, are pair-wise indistinguishable by \<oo> throughout execution and 
the program executions match/allign.


-------

definition noninterference is: given a pair of states, indistinguishable by \<oo>,
no execution of the program c (lifted to pairs of states) reaches a pair of states distinguishable by \<oo>.

definition noninterference on (liftC \<oo> c) is also a property s.t.
given a pair of states that are indistinguishable through \<oo>, of the program  (liftC \<oo> c) doesn't fail 
then all pairs of states throughout the 
execution of liftC \<oo> c are indistinguishable.

the noninterference judgement on (liftC \<oo> c) provides the same amount of information as a programming language semantics that 
is a tree T of all possible executions that can happen on pairs of states, as well as a proof that if the precondition and 
the relies hold and the precondition respects  \<oo>, then for all possible executions in the tree
   if the program doesn't fail 
    the indistinguishability predicate is preserved


(do we also want the frame condition to be preserved)

question
is there anything other than no-crash that is needed to prove non-interference and (e.g. there is no non-determinism), potentially?

if not,

prove 
theorem noninterference: 


If we can prove this, we are done (with the security paper).

question 
can we change liftC to not crash
then instead prove
>how can we generalise the lifting function liftC and instead of crashing 
 instantiate the guarantee in a way that enforces non-interference/indistinguishability?

then pro

If the preconditions are indistinguishable using \<oo>, and the lifted program  (liftC \<oo> c)  is safe,
and the preconditinos are indistinguishable using \<oo>.

If the preconditions are indistinguishable using \<oo>, and the lifted program  (liftC \<oo> c)  is safe,
and the preconditinos are indistinguishable using \<oo>.





properties (p, r) do not crash
these executions will 
and you can also extract a tree semantics that only contains 
split to two pieces, one is all possible executions, and the other is 
function to filter safe executions out of safe judgement
if there is no crashing anywhere 

define noninterference directly on liftC o C

lemma exact_security:
  fixes hl1 hl2 :: \<open>'l :: pre_perm_alg\<close>
    and hs1 hs2 :: 's
    and c :: \<open>('l \<times> 's, unit) comm\<close>
    and p q :: \<open>'l \<times> 's \<Rightarrow> bool\<close>
    and r g :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>
  shows
  \<open>safe
      (max (alength t1) (alength t2))
      (liftC \<oo> c)
      (Inl (exch4 (fst (ahd t1), fst (ahd t2))))
      (liftR r) (liftR g)
      (liftP q \<circ> exch4)
      (liftP S \<circ> exch4) (liftP F \<circ> exch4) \<Longrightarrow> f ( c, n, p, r) 
no_crashing \<and> indistinguishable everywhere through initial_s p c  \<oo>  >
*)

end