 theory SecLogic
  imports "../Soundness"
begin

text \<open>
  This file is divided into three parts.
  The first part contains the basic relational logic assertions for security reasoning.
  The second part contains the basic security predicates for relations.
  The third part is about adapting the previous notions to be compatible with RGSep.
\<close>

section \<open> Relational Security Logic \<close>

subsection \<open> Relational Predicate Lifting \<close>

\<comment> \<open> The same a \<open>pred_times\<close>, but this syntax is nicer for relational reasoning. \<close>

abbreviation(input) lift_preds ("\<lblot> _ \<bar> _ \<rblot>" [0,0]) where
  \<open>\<lblot> p \<bar> q \<rblot> \<equiv> p \<times>\<^sub>P q\<close>

abbreviation lift_pred ("\<lblot> _ \<rblot>" [0]) where
  \<open>\<lblot> p \<rblot> \<equiv> p \<times>\<^sub>P p\<close>

lemmas lift_pred_def = pred_times_def[of p p for p]


subsubsection \<open> Predicate Lifting Lemmas \<close>

lemma lift_pred_sup_semidistrib:
  \<open>\<lblot>p\<rblot> \<squnion> \<lblot>q\<rblot> \<le> \<lblot>p \<squnion> q\<rblot>\<close>
  by (simp add: le_fun_def)

lemma pred_list_disj_eq:
  \<open>\<lblot> p \<squnion> q \<rblot> = \<lblot> p \<rblot> \<squnion> \<lblot> p \<bar> q \<rblot> \<squnion> \<lblot> q \<bar> p \<rblot> \<squnion> \<lblot> q \<rblot>\<close>
  by (force simp add: fun_eq_iff)

lemma lift_pred_Sup_semidistrib:
  \<open>(\<Squnion>p\<in>P. \<lblot>p\<rblot>) \<le> \<lblot>\<Squnion>P\<rblot>\<close>
  by (force simp add: le_fun_def)

lemma lift_pred_inf_distrib:
  \<open>\<lblot>p \<sqinter> q\<rblot> = \<lblot>p\<rblot> \<sqinter> \<lblot>q\<rblot>\<close>
  by (force simp add: fun_eq_iff)

lemma lift_pred_Inf_distrib:
  \<open>\<lblot>\<Sqinter>P\<rblot> = (\<Sqinter>p\<in>P. \<lblot>p\<rblot>)\<close>
  by (force simp add: fun_eq_iff)

lemma lift_pred_not_semidistrib:
  \<open>\<lblot>- p\<rblot> \<le> - \<lblot>p\<rblot>\<close>
  by (force simp add: fun_eq_iff)

lemma lift_pred_sepconj_distrib:
  fixes p q :: \<open>'a ::pre_perm_alg \<Rightarrow> bool\<close>
  shows \<open>\<lblot>p \<^emph> q\<rblot> = \<lblot>p\<rblot> \<^emph> \<lblot>q\<rblot>\<close>
  by (force simp add: fun_eq_iff sepconj_def)

lemma lift_pred_emp_distrib[simp]:
  \<open>\<lblot>emp\<rblot> = emp\<close>
  by (force simp add: fun_eq_iff emp_def)

thm top_pred_times_top_eq
thm bot_pred_times_eq pred_times_bot_eq

lemma not_pred_times_of_not_eq:
  \<open>- \<lblot> - p \<bar> - q  \<rblot> = (p \<circ> fst) \<squnion> (q \<circ> snd)\<close>
  by (simp add: fun_eq_iff)

lemma neg_pred_times_of_neg_iff:
  \<open>\<not> \<lblot> \<lambda>x. \<not> p x \<bar> \<lambda>x. \<not> q x \<rblot> x \<longleftrightarrow> ((p \<circ> fst) \<squnion> (q \<circ> snd)) x\<close>
  by (simp add: fun_eq_iff pred_times_def)


subsection \<open> Agreement \<close>

definition sec_agree :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool\<close> (\<open>\<bbbA>\<close>) where
  \<open>\<bbbA> vf \<equiv> (\<lambda>(x,y). vf x = vf y)\<close>


lemma conj_agree_iff:
  \<open>\<bbbA> v1 \<sqinter> \<bbbA> v2 = \<bbbA> (\<lambda>x. (v1 x, v2 x))\<close>
  by (simp add: sec_agree_def comp_def fun_eq_iff split: prod.splits)

lemma agree_not_pred_eq[simp]:
  \<open>\<bbbA> (\<lambda>s. \<not> p s) = \<bbbA> p\<close>
  by (simp add: sec_agree_def)


subsection \<open> Relational Lifting of Relations \<close>

text \<open>
Here I mean "relation\<^emph>\<open>al\<close>" as "on pairs" and "relation" as functions of two arguments to \<^typ>\<open>bool\<close>.
\<close>

abbreviation(input) lift_rels (\<open>\<lblot> _ \<bar> _ \<rblot>\<^sub>R\<close>) where
  \<open>\<lblot> ra \<bar> rb \<rblot>\<^sub>R \<equiv> ra \<times>\<^sub>R rb\<close>

abbreviation lift_rel (\<open>\<lblot> _ \<rblot>\<^sub>R\<close>) where
  \<open>\<lblot> r \<rblot>\<^sub>R \<equiv> r \<times>\<^sub>R r\<close>

lemmas lift_rel_def = rel_times_def[of r r for r]


lemma pre_state_lift_rel_eq[simp]:
  \<open>pre_state \<lblot> r \<rblot>\<^sub>R = \<lblot> pre_state r \<rblot>\<close>
  by (simp add: fun_eq_iff pre_state_def)


subsection \<open> Command Lifting \<close>

abbreviation lift_comm :: \<open>'s comm \<Rightarrow> ('s \<times> 's) comm\<close> where
  \<open>lift_comm \<equiv> map_atom lift_rel\<close>


subsection \<open> Unlifting Predicates \<close>

text \<open>
We take the relational \<^emph>\<open>un\<close>lifting by considering only the pairs with the same state on both sides.
This is sometimes called the "diagonal" map, hence the use of delta.
We will call them "same-pair" states.
\<close>

definition unlift_pred :: \<open>('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>unlift_pred p \<equiv> p \<circ> \<Delta>\<close>


lemma unlift_pred_bot_eq[simp]:
  \<open>unlift_pred \<bottom> = \<bottom>\<close>
  by (simp add: unlift_pred_def fun_eq_iff)

lemma unlift_pred_top_eq[simp]:
  \<open>unlift_pred \<top> = \<top>\<close>
  by (simp add: unlift_pred_def fun_eq_iff)

lemma unlift_lift_eq[simp]:
  \<open>unlift_pred \<lblot> p \<rblot> = p\<close>
  by (simp add: unlift_pred_def fun_eq_iff)


subsection \<open> Unlifting Relations \<close>

definition unlift_rel :: \<open>('a \<times> 'a \<Rightarrow> 'b \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)\<close> where
  \<open>unlift_rel r \<equiv> \<lambda>x y. r (\<Delta> x) (\<Delta> y)\<close>


lemma unlift_rel_bot_eq[simp]:
  \<open>unlift_rel \<bottom> = \<bottom>\<close>
  by (simp add: unlift_rel_def fun_eq_iff)

lemma unlift_rel_KFalse_eq[simp]:
  \<open>unlift_rel (\<lambda>_ _. False) = \<bottom>\<close>
  by (simp add: unlift_rel_def fun_eq_iff)

lemma unlift_rel_top_eq[simp]:
  \<open>unlift_rel \<top> = \<top>\<close>
  by (simp add: unlift_rel_def fun_eq_iff)

lemma unlift_rel_KTrue_eq[simp]:
  \<open>unlift_rel (\<lambda>_ _. True) = \<top>\<close>
  by (simp add: unlift_rel_def fun_eq_iff)

lemma unlift_rel_eqrel_eq[simp]:
  \<open>unlift_rel (=) = (=)\<close>
  by (simp add: unlift_rel_def fun_eq_iff)

lemma pre_state_unlift_rel_then_unlift_pred_pre_state:
  \<open>pre_state (unlift_rel r) \<le> unlift_pred (pre_state r)\<close>
  by (force simp add: le_fun_def pre_state_def unlift_pred_def unlift_rel_def)


section \<open> Information-Flow Notions on Relations \<close>

text \<open>
There are a number of properties to consider about a relation to determine its information-flow
effects.
\<close>

subsection \<open> Quasi-reflexive Preserving Relations \<close>

text \<open>
Picks out the states such that any quasi-reflexive predicate that is a subset of these states
is still quasireflexive after taking the strongest postcondition.

This is a healthiness condition: a good info-flow relation should satisfy this everywhere.
\<close>

definition
  \<open>quasirefl_preserv r \<equiv> univ_states (r \<rightarrow> \<lblot> unlift_rel r \<rblot>\<^sub>R)\<close>

lemma quasirefl_preserv_eq:
  \<open>quasirefl_preserv r = (\<lambda>(ax, ay).
    \<forall>ax' ay'. r (ax, ay) (ax', ay') \<longrightarrow> r (\<Delta> ax) (\<Delta> ax') \<and> r (\<Delta> ay) (\<Delta> ay'))\<close>
  by (simp add: quasirefl_preserv_def pre_state_def unlift_rel_def fun_eq_iff univ_states_def)

lemma quasirefl_preserv_preserves_quasireflp:
  \<open>p \<le> quasirefl_preserv r \<Longrightarrow>
    quasireflp (curry p) \<Longrightarrow> quasireflp (curry (sp r p))\<close>
  by (simp add: quasirefl_preserv_eq quasireflp_iff sp_def le_fun_def) blast

lemma quasirefl_preserv_lift_rel:
  \<open>\<top> \<le> quasirefl_preserv \<lblot> r \<rblot>\<^sub>R\<close>
  by (force simp add: rel_times_def quasirefl_preserv_eq split: prod.splits)

lemma quasirefl_preserv_then_prestate_prod_eq:
  \<open>\<top> \<le> quasirefl_preserv r \<circ> \<Delta> \<Longrightarrow>
    pre_state \<lblot> unlift_rel r \<rblot>\<^sub>R = \<lblot> unlift_pred (pre_state r) \<rblot>\<close>
  by (simp add: fun_eq_iff le_fun_def unlift_rel_def unlift_pred_def pre_state_def
      quasirefl_preserv_eq) blast


subsection \<open> Symmetry Preserving Relations \<close>

text \<open>
Picks out the states such that any symmetric predicate that is a subset of these states
is still quasireflexive after taking the strongest postcondition.

This is a healthiness condition: a good info-flow relation should satisfy this everywhere.
\<close>

definition exchange :: \<open>'a \<times> 'b \<Rightarrow> 'b \<times> 'a\<close> (\<open>\<^bold>X\<close>) where
  \<open>\<^bold>X \<equiv> \<lambda>(a,b). (b,a)\<close>

lemma exchange_apply[simp]: \<open>\<^bold>X (a, b) = (b, a)\<close>
  by (simp add: exchange_def)


definition
  \<open>sym_preserv r \<equiv> univ_states (r \<leftrightarrow> (r \<circ>\<^sub>2 \<^bold>X))\<close>

lemma sym_preserv_eq:
  \<open>sym_preserv r = (\<lambda>(sx, sy).
    (\<forall>sx' sy'. r (sx,sy) (sx',sy') \<longleftrightarrow> r (sy,sx) (sy',sx')))\<close>
  by (simp add: sym_preserv_def fun_eq_iff pre_state_def exchange_def univ_states_def)


lemma symp_prestate_preserves_symp_fwd:
  \<open>p \<le> sym_preserv r \<Longrightarrow> symp (curry p) \<Longrightarrow> symp (curry (sp r p))\<close>
  by (fastforce simp add: sym_preserv_eq symp_def sp_def)

lemma sym_preserv_lift_rel:
  \<open>\<top> \<le> sym_preserv \<lblot> r \<rblot>\<^sub>R\<close>
  by (force simp add: sym_preserv_eq)


subsection \<open> Quasi-reflexive and Symmetric Closed States \<close>

definition \<open>quasireflcl_states p \<equiv> p \<rightarrow> \<lblot> p \<circ> \<Delta> \<rblot>\<close>
definition \<open>symcl_states p \<equiv> p \<leftrightarrow> (p \<circ> \<^bold>X)\<close>


lemma quasireflcl_states_eq:
  \<open>quasireflcl_states p = (\<lambda>(x,y). p (x, y) \<longrightarrow> p (x, x) \<and> p (y, y))\<close>
  by (simp add: quasireflcl_states_def fun_eq_iff)

lemma symcl_states_eq:
  \<open>symcl_states p = (\<lambda>(x,y). p (x, y) \<longleftrightarrow> p (y, x))\<close>
  by (simp add: symcl_states_def fun_eq_iff)

lemma quasireflcl_states_sec_agree_eq[simp]:
  \<open>quasireflcl_states (\<bbbA> f) = \<top>\<close>
  by (force simp add: quasireflcl_states_def sec_agree_def)

lemma quasireflcl_states_neg_sec_agree_eq[simp]:
  \<open>quasireflcl_states (- \<bbbA> f) = \<bbbA> f\<close>
  by (force simp add: quasireflcl_states_def sec_agree_def)

lemma symcl_states_of_not_eq[simp]:
  \<open>symcl_states (- p) = symcl_states p\<close>
  by (simp add: fun_eq_iff symcl_states_def)


subsection \<open> Non-Revealing \<close>

text \<open>
Starting from the non-revealing states of a relation does not reveal any information
about those states. In essence, the relation restricted to those states is defined entirely by
the steps on the same-pair states.
\<close>

definition \<open>nonrevealing r \<equiv> univ_states (\<lblot> unlift_rel r \<rblot>\<^sub>R \<rightarrow> r)\<close>
abbreviation \<open>revealing \<equiv> - nonrevealing\<close>

lemma nonrevealing_eq:
  \<open>nonrevealing r = (\<lambda>(sx, sy).
    \<forall>sx' sy'. r (\<Delta> sx) (\<Delta> sx') \<and> r (\<Delta> sy) (\<Delta> sy') \<longrightarrow> r (sx, sy) (sx', sy'))\<close>
  by (simp add: nonrevealing_def univ_states_eq fun_eq_iff unlift_rel_def)

lemma revealing_alt_eq:
  \<open>revealing r = pre_state (\<lblot> unlift_rel r \<rblot>\<^sub>R \<sqinter> -r)\<close>
  by (simp add: nonrevealing_def)


lemma nonrevealing_of_bot_eq[simp]:
  \<open>nonrevealing \<bottom> = \<top>\<close>
  by (simp add: fun_eq_iff nonrevealing_eq)

lemma nonrevealing_of_eqrel_eq[simp]:
  \<open>nonrevealing (=) = \<top>\<close>
  by (simp add: fun_eq_iff nonrevealing_eq)


text \<open>
This next theorem is important to justifying the security of the entire system.
On steps starting in non-relational states, the atomic step acts
\<^emph>\<open>as if\<close> it were a product relation. Thus it does not leak information.
\<close>

theorem nonrevealing_top_eq:
  \<open>nonrevealing r = univ_states (\<lblot> unlift_rel r \<rblot>\<^sub>R \<rightarrow> r)\<close>
  by (simp add: nonrevealing_eq unlift_rel_def univ_states_def pre_state_def fun_eq_iff)

lemma nonrevealing_rel_conj_merge:
  \<open>nonrevealing a q \<sqinter> nonrevealing b q \<le> nonrevealing (a \<sqinter> b) q\<close>
  by (simp add: nonrevealing_eq) blast

lemma quasireflp_preserv_then_nonrevealing_iff:
  \<open>quasirefl_preserv r \<sqinter> nonrevealing r = univ_states (\<lblot> unlift_rel r \<rblot>\<^sub>R \<leftrightarrow> r)\<close>
  by (simp add: quasirefl_preserv_def nonrevealing_def latiff_def univ_states_inf_distrib
      impl_def inf_commute sup_commute)


section \<open> Same State Non-relational \<close>

text \<open>
In particular, a good info-flow program should be non-revealing starting from any same-pair state.
This is another healthiness condition.
\<close>

definition
  \<open>same_state_nonrevealing r \<equiv> \<top> \<le> nonrevealing r \<circ> \<Delta>\<close>

lemma same_state_nonrevealing_iff:
  \<open>same_state_nonrevealing r \<longleftrightarrow>
    (\<forall>s sx' sy'. r (s, s) (sx', sx') \<and> r (s, s) (sy', sy') \<longrightarrow> r (s, s) (sx', sy'))\<close>
  by (simp add: same_state_nonrevealing_def nonrevealing_eq quasirefl_preserv_eq le_fun_def)

lemma same_state_nonrevealing_iff_eqn:
  \<open>same_state_nonrevealing r \<longleftrightarrow> \<lblot> unlift_rel r \<rblot>\<^sub>R \<sqinter> pretest (case_prod (=)) \<le> r\<close>
  by (simp add: same_state_nonrevealing_def nonrevealing_def quasirefl_preserv_def
      le_fun_def fun_eq_iff univ_states_eq)

lemma same_state_nonrevealing_conjI:
  \<open>same_state_nonrevealing ra \<Longrightarrow> same_state_nonrevealing rb \<Longrightarrow>
    same_state_nonrevealing (ra \<sqinter> rb)\<close>
  using nonrevealing_rel_conj_merge
  by (fastforce simp add: same_state_nonrevealing_def)

lemma same_state_nonrevealing_lift_rel:
  \<open>same_state_nonrevealing \<lblot> r \<rblot>\<^sub>R\<close>
  by (clarsimp simp add: same_state_nonrevealing_def nonrevealing_eq)


section \<open> Non-declassifying \<close>

text \<open>
Declassification is the intentional release of secret information to the public.
In a relational partial-safety semantics, this information release can be achieved via blocking.
The idea is that we block whenever the information to be revealed disagrees on either sides
of the pair, and thus discard any execution where the information does not match.

A relation is \<^emph>\<open>non\<close>declassifying if every paired-state step it can take is justified by the
existence of two self-state paired steps from that same initial state.
This rules out the paired-state relation blocking when the two self-paired states may proceed.
\<close>

definition \<open>nondeclassifying r \<equiv> \<lblot> unlift_pred (pre_state r) \<rblot> \<rightarrow> pre_state r\<close>
abbreviation \<open>declassifying \<equiv> - nondeclassifying\<close>

lemma nondeclassifying_eq:
  \<open>nondeclassifying r = (\<lambda>(sx, sy).
    Ex (r (\<Delta> sx)) \<longrightarrow> Ex (r (\<Delta> sy)) \<longrightarrow> Ex (r (sx, sy)))\<close>
  by (simp add: nondeclassifying_def unlift_pred_def pre_state_def fun_eq_iff) blast

lemma nondeclassifying_rel_times:
  \<open>nondeclassifying \<lblot> r \<rblot>\<^sub>R = \<top>\<close>
  by (simp add: nondeclassifying_def fun_eq_iff)

lemma nondeclassifying_of_bot_eq[simp]:
  \<open>nondeclassifying \<bottom> = \<top>\<close>
  by (simp add: fun_eq_iff nondeclassifying_def)

lemma nondeclassifying_of_eqrel_eq[simp]:
  \<open>nondeclassifying (=) = \<top>\<close>
  by (simp add: fun_eq_iff nondeclassifying_def)


subsection \<open> Enabled Splitting \<close>

text \<open>
Another property is that if a paired-state step is possible,
then a step can be taken from the same-pair states.

This is a very weak notion, already implied by quasi-reflexive preservation.
(Which we have already set as a healthiness condition.)

However, the concept is interesting because it is also implied by
non-declassification, whereas quasi-reflexive preservation is unrelated
to non-declassification and non-revelation.
\<close>

definition
  \<open>enabled_split r \<equiv> \<lambda>(sx, sy).
    Ex (r (sx, sy)) \<longrightarrow> Ex (r (\<Delta> sx)) \<and> Ex (r (\<Delta> sy))\<close>


lemma enabled_split_iff_enabled_le_product_enabled_pred:
    \<open>p \<le> enabled_split r \<longleftrightarrow>
      pre_state r \<sqinter> p \<le> \<lblot> unlift_pred (pre_state r) \<rblot> \<sqinter> p\<close>
  by (simp add: enabled_split_def unlift_pred_def pre_state_def le_fun_def) blast

lemma enabled_split_iff_enabled_le_enabled_product_rel:
  assumes \<open>p \<le> quasirefl_preserv r\<close>
  shows
    \<open>p \<le> enabled_split r \<longleftrightarrow>
      pre_state r \<sqinter> p \<le> pre_state \<lblot> unlift_rel r \<rblot>\<^sub>R \<sqinter> p\<close>
  using assms
  by (simp add: enabled_split_def unlift_rel_def quasirefl_preserv_eq pre_state_def le_fun_def)
    blast

lemma quasirefl_preserv_implies_rel_split:
  \<open>quasirefl_preserv \<le> enabled_split\<close>
  by (simp add: quasirefl_preserv_eq enabled_split_def le_fun_def) blast


subsection \<open> Secure Relations \<close>

text \<open> A relation is secure when it is either declassifying or non-revealing. \<close>

definition \<open>secure_rel a \<equiv> declassifying a \<squnion> nonrevealing a\<close>

lemma secure_rel_eq:
  \<open>secure_rel r = (\<lambda>(x,y).
    (\<exists>xa' xb'. r (\<Delta> x) (xa', xb')) \<and>
      (\<exists>ya' yb'. r (\<Delta> y) (ya', yb')) \<and>
      (\<forall>x' y'. \<not> r (x, y) (x', y')) \<or>
    (\<forall>x' y'. r (\<Delta> x) (\<Delta> x') \<and> r (\<Delta> y) (\<Delta> y') \<longrightarrow> r (x, y) (x', y')))\<close>
  by (simp add: secure_rel_def nondeclassifying_eq nonrevealing_eq fun_eq_iff)
    blast

lemma secure_rel_relconj_distrib:
  \<open>secure_rel a \<sqinter> secure_rel b \<le> secure_rel (a \<sqinter> b)\<close>
  by (clarsimp simp add: secure_rel_def nondeclassifying_def nonrevealing_eq enabled_split_def
      pre_state_def unlift_pred_def) blast

lemma secure_rel_of_bot_eq[simp]:
  \<open>secure_rel \<bottom> = \<top>\<close>
  by (simp add: secure_rel_def fun_eq_iff)

lemma secure_rel_of_eqrel_eq[simp]:
  \<open>secure_rel (=) = \<top>\<close>
  by (simp add: secure_rel_def fun_eq_iff)


section \<open> Security Reasoning for RGSep States and Relations \<close>

text \<open>
  The issue with the GenRGSep framework for security reasoning is that it expects
  the local and shared states to be in a particular location in a pair.
  The security reasoning also requires the state to be in a pair,
  but in the wrong order for GenRGSep.

  Here we bridge that gap by tedious alternate definitions that rearrange the states.
\<close>


type_synonym ('a,'b) rgsep_secstate = \<open>(('a \<times> 'a) \<times> ('b \<times> 'b))\<close>

type_synonym ('a,'b) sec_rgsepstate = \<open>(('a \<times> 'b) \<times> ('a \<times> 'b))\<close>


subsection \<open> Exchange \<close>

text \<open>
A function to exchange the GenRGSep view of security states with
the security view of GenRGSep states.
Thankfully it works both ways.
\<close>

definition exch4 (\<open>\<ddagger>\<close>) where
  \<open>\<ddagger> abcd \<equiv> ((fst (fst abcd), fst (snd abcd)), (snd (fst abcd), snd (snd abcd)))\<close>


lemma exch4_four_apply[simp]:
  \<open>\<ddagger> ((a,b),(c,d)) = ((a,c),(b,d))\<close>
  by (simp add: exch4_def)

lemma exch4_two_apply:
  \<open>\<ddagger> (sx, sy) = ((fst sx, fst sy), (snd sx, snd sy))\<close>
  by (simp add: exch4_def)

lemma exch4_apply:
  \<open>\<ddagger> abcd = ((fst (fst abcd), fst (snd abcd)), (snd (fst abcd), snd (snd abcd)))\<close>
  by (simp add: exch4_def)

lemma exch4_idem[simp]:
  \<open>\<ddagger> (\<ddagger> x) = x\<close>
  by (simp add: exch4_def split: prod.splits)

lemma exch4_switch:
  \<open>\<ddagger> x = y \<longleftrightarrow> x = \<ddagger> y\<close>
  by (force simp add: exch4_def split: prod.splits)

lemma exch4_comp_idem[simp]:
  \<open>\<ddagger> \<circ> \<ddagger> = id\<close>
  by (force simp add: exch4_def)

lemma leq_exch4_shunt:
  \<open>p \<le> q \<circ> \<ddagger> \<longleftrightarrow> p \<circ> \<ddagger> \<le> q\<close>
  by (metis comp_def exch4_idem le_fun_def)

lemma le_comp_exch4_iff[simp]:
  \<open>f \<circ> \<ddagger> \<le> g \<circ> \<ddagger> \<longleftrightarrow> f \<le> g\<close>
  by (force simp add: le_fun_def)

lemma exch4_eq_iff[simp]:
  \<open>\<ddagger> a = \<ddagger> b \<longleftrightarrow> a = b\<close>
  by (cases a, cases b, force simp add: exch4_def)

lemma comp_exch4_eq_iff[simp]:
  \<open>f \<circ> \<ddagger> = g \<circ> \<ddagger> \<longleftrightarrow> f = g\<close>
  by (simp add: fun_eq_iff, blast)

lemma rel_comp_exch4_eq_iff[simp]:
  \<open>ra \<circ>\<^sub>2 \<ddagger> = rb \<circ>\<^sub>2 \<ddagger> \<longleftrightarrow> ra = rb\<close>
  by (force simp add: fun_eq_iff)

lemma prod_destruct_exch4_eq[simp]:
  \<open>fst (fst (\<ddagger> x)) = fst (fst x)\<close>
  \<open>fst (snd (\<ddagger> x)) = snd (fst x)\<close>
  \<open>snd (fst (\<ddagger> x)) = fst (snd x)\<close>
  \<open>snd (snd (\<ddagger> x)) = snd (snd x)\<close>
  by (clarsimp simp add: exch4_def)+

lemma prod_part_destruct_exch4_eq[simp]:
  \<open>fst (\<ddagger> (ab, cd)) = (fst ab, fst cd)\<close>
  \<open>snd (\<ddagger> (ab, cd)) = (snd ab, snd cd)\<close>
  by (simp add: exch4_def)+

lemma eq_exch4_iff[simp]:
  \<open>((ax, bx), (ay, by)) = \<ddagger> ab \<longleftrightarrow> fst ab = (ax, ay) \<and> snd ab = (bx, by)\<close>
  by (force simp add: exch4_def split: prod.splits)

lemma le_comp_exch4_iff2[simp]:
  \<open>(\<lambda>x. f (\<ddagger> x)) \<le> (\<lambda>x. g (\<ddagger> x)) \<longleftrightarrow> f \<le> g\<close>
  by (force simp add: le_fun_def)

lemma inv_exch4_eq[simp]:
  \<open>inv \<ddagger> = \<ddagger>\<close>
  by (simp add: inv_unique_comp)

lemma exch4_inj[simp]:
  \<open>inj \<ddagger>\<close>
  by (clarsimp simp add: inj_iff)

lemma exch4_surj[simp]:
  \<open>surj \<ddagger>\<close>
  by (clarsimp simp add: surj_iff fun_eq_iff)

lemma exch4_bij[simp]:
  \<open>bij \<ddagger>\<close>
  by (simp add: bijI)

lemma top_pred_comp2_exch4_eq[simp]:
  \<open>(\<top> \<circ> \<ddagger>) = \<top>\<close>
  by (simp add: fun_eq_iff)

lemma top_rel_comp2_exch4_eq[simp]:
  \<open>(\<top> \<circ>\<^sub>2 \<ddagger>) = \<top>\<close>
  by (simp add: fun_eq_iff)

lemma bot_pred_comp2_exch4_eq[simp]:
  \<open>(\<bottom> \<circ> \<ddagger>) = \<bottom>\<close>
  by (simp add: fun_eq_iff)

lemma bot_rel_comp2_exch4_eq[simp]:
  \<open>(\<bottom> \<circ>\<^sub>2 \<ddagger>) = \<bottom>\<close>
  by (simp add: fun_eq_iff)

lemma eqrel_comp2_exch4_eq[simp]:
  \<open>((=) \<circ>\<^sub>2 \<ddagger>) = (=)\<close>
  by (simp add: fun_eq_iff)

lemma all_imp_exch4_rel_iff_all_exch4_imp_rel:
  \<open>(\<forall>r. P r \<longrightarrow> Q (r \<circ>\<^sub>2 \<ddagger>)) \<longleftrightarrow> (\<forall>r. P (r \<circ>\<^sub>2 \<ddagger>) \<longrightarrow> Q r)\<close>
  by (metis comp2_fusion comp2_id exch4_comp_idem)

lemma top_le_comp_exch4_iff[simp]:
  \<open>\<top> \<le> p \<circ> \<ddagger> \<longleftrightarrow> \<top> \<le> p\<close>
  by (simp add: leq_exch4_shunt)

lemma comp2_exch4_leq_shunt:
  \<open>a \<circ>\<^sub>2 \<ddagger> \<le> b \<longleftrightarrow> a \<le> b \<circ>\<^sub>2 \<ddagger>\<close>
  by (simp add: le_fun_def) blast


subsection \<open> Exchanged Predicate Lifting \<close>

definition lift_preds_exch4 (\<open>\<lblot> _ \<bar> _ \<rblot>\<^sub>\<ddagger>\<close> [0]) where
  \<open>\<lblot> p \<bar> q \<rblot>\<^sub>\<ddagger> \<equiv> \<lblot> p \<bar> q \<rblot> \<circ> exch4\<close>

abbreviation lift_pred_exch4 (\<open>\<lblot> _ \<rblot>\<^sub>\<ddagger>\<close> [0]) where
  \<open>\<lblot> p \<rblot>\<^sub>\<ddagger> \<equiv> \<lblot> p \<bar> p \<rblot>\<^sub>\<ddagger>\<close>

lemmas lift_pred_exch4_def = lift_preds_exch4_def[of p p for p]


lemma lift_preds_exch4_exch4_eq[simp]:
  \<open>\<lblot> p \<bar> q \<rblot>\<^sub>\<ddagger> (\<ddagger> s) = \<lblot> p \<bar> q \<rblot> s\<close>
  by (simp add: lift_preds_exch4_def pred_times_def exch4_def split: prod.splits)

lemma lift_preds_exch4_apply_pair:
  \<open>\<lblot> p \<bar> q \<rblot>\<^sub>\<ddagger> (a, b) = (p (fst a, fst b) \<and> q (snd a, snd b))\<close>
  by (simp add: lift_preds_exch4_def pred_times_def exch4_def split: prod.splits)

lemma lift_preds_exch4_apply_four:
  \<open>\<lblot> p \<bar> q \<rblot>\<^sub>\<ddagger> ((a, b), (c, d)) = \<lblot> p \<bar> q \<rblot> ((a, c), (b, d))\<close>
  by (simp add: lift_preds_exch4_def exch4_def)

lemma lift_preds_exch4_apply:
  \<open>\<lblot> p \<bar> q \<rblot>\<^sub>\<ddagger> ((a, b), (c, d)) \<longleftrightarrow> p (a,c) \<and> q (b,d)\<close>
  by (simp add: lift_preds_exch4_def exch4_def)

lemma lift_pred_exch4_mono:
  \<open>p \<le> q \<Longrightarrow> \<lblot> p \<rblot>\<^sub>\<ddagger> \<le> \<lblot> q \<rblot>\<^sub>\<ddagger>\<close>
  by (simp add: lift_preds_exch4_def le_fun_def)

lemma lift_pred_exch4_mono_exch4:
  \<open>\<lblot> p \<rblot> \<le> \<lblot> q \<rblot> \<Longrightarrow> \<lblot> p \<rblot>\<^sub>\<ddagger> \<le> \<lblot> q \<rblot>\<^sub>\<ddagger>\<close>
  by (force simp add: lift_pred_exch4_def le_fun_def)

lemma lift_pred_exch4_sepconj_conj_distrib:
  \<open>\<lblot>p \<^emph>\<and> q\<rblot>\<^sub>\<ddagger> = \<lblot>p\<rblot>\<^sub>\<ddagger> \<^emph>\<and> \<lblot>q\<rblot>\<^sub>\<ddagger>\<close>
  by (force simp add: lift_pred_exch4_def fun_eq_iff sepconj_conj_apply)

lemma lift_pred_exch4_disj_semidistrib:
  \<open>\<lblot> p \<rblot>\<^sub>\<ddagger> \<squnion> \<lblot> q \<rblot>\<^sub>\<ddagger> \<le> \<lblot> p \<squnion> q \<rblot>\<^sub>\<ddagger>\<close>
  by (force simp add: lift_pred_exch4_def fun_eq_iff)

lemma lift_pred_exch4_localpred_distrib:
  \<open>\<lblot> \<L> p \<rblot>\<^sub>\<ddagger> = \<L> (\<lblot>p\<rblot>)\<close>
  by (force simp add: lift_pred_exch4_def)

lemma lift_pred_exch4_sharedpred_distrib:
  \<open>\<lblot> \<S> p \<rblot>\<^sub>\<ddagger> = \<S> (\<lblot>p\<rblot>)\<close>
  by (force simp add: lift_pred_exch4_def)

lemma Sup_lift_pred_exch4_semidistrib:
  \<open>\<Squnion>(lift_pred_exch4 ` P) \<le> \<lblot> \<Squnion>P \<rblot>\<^sub>\<ddagger>\<close>
  by (force simp add: lift_pred_exch4_def)

lemma lift_pred_exch4_Inf_distrib:
  \<open>\<lblot> \<Sqinter>P \<rblot>\<^sub>\<ddagger> = \<Sqinter>(lift_pred_exch4 ` P)\<close>
  by (force simp add: lift_pred_exch4_def)

lemma sswa_lift_pred_exch4_semidistrib:
  \<open>sswa (R \<times>\<^sub>R R) \<lblot> p \<rblot>\<^sub>\<ddagger> \<le> \<lblot> sswa R p \<rblot>\<^sub>\<ddagger>\<close>
  apply (clarsimp simp add: fun_eq_iff lift_pred_exch4_def sp_def)
  apply (metis predicate2D rel_times_apply' rel_times_rtranclp_semidistrib)
  done

lemma sswa_sup_rel_lift_pred_exch4_semidistrib:
  \<open>sswa (ra \<times>\<^sub>R ra \<squnion> rb \<times>\<^sub>R rb) \<lblot> p \<rblot>\<^sub>\<ddagger> \<le> \<lblot> sswa (ra \<squnion> rb) p \<rblot>\<^sub>\<ddagger>\<close>
  apply (clarsimp simp add: fun_eq_iff lift_pred_exch4_def sp_def)
  apply (metis predicate2D rel_times_apply' rel_times_rtranclp_semidistrib rtranclp_mono
      rel_times_sup_semidistrib)
  done

lemma wssa_lift_pred_exch4_semidistrib:
  \<open>\<lblot> wssa R p \<rblot>\<^sub>\<ddagger> \<le> wssa (R \<times>\<^sub>R R) \<lblot> p \<rblot>\<^sub>\<ddagger>\<close>
  apply (clarsimp simp add: fun_eq_iff lift_pred_exch4_def wlp_def)
  apply (metis fst_conv rel_times_def rtranclp_tuple_rel_semidistrib snd_conv)
  done

lemma wssa_reltimes_lift_pred_exch4_wssa_eq_lift_pred_exch4_wssa[simp]:
  \<open>wssa (R \<times>\<^sub>R R) \<lblot> wssa R p \<rblot>\<^sub>\<ddagger> = \<lblot> wssa R p \<rblot>\<^sub>\<ddagger>\<close>
  apply (clarsimp simp add: wlp_def lift_pred_exch4_def fun_eq_iff)
  apply (metis rel_times_def rtranclp.rtrancl_refl rtranclp_trans rtranclp_tuple_rel_semidistrib
      fst_conv snd_conv)
  done

lemma sswa_reltimes_lift_pred_exch4_sswa_eq_lift_pred_exch4_sswa[simp]:
  \<open>sswa (R \<times>\<^sub>R R) \<lblot> sswa R p \<rblot>\<^sub>\<ddagger> = \<lblot> sswa R p \<rblot>\<^sub>\<ddagger>\<close>
  apply (clarsimp simp add: sp_def lift_pred_exch4_def fun_eq_iff)
  apply (metis rel_times_def rtranclp.rtrancl_refl rtranclp_trans rtranclp_tuple_rel_semidistrib
      fst_conv snd_conv)
  done


subsection \<open> Exchanged Relation Lifting \<close>

definition lift_rel_exch4 (\<open>\<lblot> _ \<rblot>\<^sub>R\<^sub>\<ddagger>\<close>) where
  \<open>\<lblot> r \<rblot>\<^sub>R\<^sub>\<ddagger> \<equiv> \<lblot> r \<rblot>\<^sub>R \<circ>\<^sub>2 \<ddagger>\<close>

lemmas lift_rel_exch4_eq = lift_rel_exch4_def[simplified lift_rel_def]

lemma lift_rel_exch4_apply[simp]:
  \<open>lift_rel_exch4 r ((ax,ay),(bx,by)) ((ax',ay'),(bx',by')) =
    (r (ax,bx) (ax',bx') \<and> r (ay,by) (ay',by'))\<close>
  by (simp add: lift_rel_exch4_def)

lemma lift_rel_exch4_apply_exch4_eq[simp]:
  \<open>lift_rel_exch4 r (\<ddagger> x) (\<ddagger> y) = \<lblot> r \<rblot>\<^sub>R x y\<close>
  by (simp add: lift_rel_exch4_def fun_eq_iff)

lemma lift_rel_exch4_comp2_exch4_eq[simp]:
  \<open>lift_rel_exch4 r \<circ>\<^sub>2 \<ddagger> = \<lblot> r \<rblot>\<^sub>R\<close>
  by (simp add: lift_rel_exch4_def fun_eq_iff)


subsection \<open> Exchanged Agreement \<close>

definition sec_agree_exch4 :: \<open>('l \<times> 's \<Rightarrow> 'v) \<Rightarrow> ('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool\<close> (\<open>\<bbbA>\<^sub>\<ddagger>\<close>) where
  \<open>\<bbbA>\<^sub>\<ddagger> h \<equiv> \<bbbA> h \<circ> exch4\<close>

lemmas sec_agree_exch4_eq = sec_agree_exch4_def[simplified sec_agree_def]

lemma sec_agree_exch4_exch4_eq[simp]:
  \<open>\<bbbA>\<^sub>\<ddagger> h (\<ddagger> s) = \<bbbA> h s\<close>
  by (simp add: sec_agree_exch4_def)

lemma sec_agree_exch4_comp_exch4_eq[simp]:
  \<open>\<bbbA>\<^sub>\<ddagger> h \<circ> \<ddagger> = \<bbbA> h\<close>
  by (simp add: sec_agree_exch4_def fun_eq_iff)


subsection \<open> Exchanged Command Lifting \<close>

abbreviation lift_comm_exch4 :: \<open>('l \<times> 's) comm \<Rightarrow> (('l \<times> 'l) \<times> ('s \<times> 's)) comm\<close> where
  \<open>lift_comm_exch4 \<equiv> map_atom lift_rel_exch4\<close>


lemmas lift_comm_exch4_rev_iff[simp] =
  map_atom_rev_iff[of lift_rel_exch4, simplified map_atom.simps[symmetric]]
  map_atom_rev_iff[of lift_rel_exch4, simplified map_atom.simps[symmetric], THEN trans[OF eq_commute]]

lemma comm_lift_exch4_eq_iff[simp]:
  \<open>lift_comm_exch4 ca = lift_comm_exch4 cb \<longleftrightarrow> ca = cb\<close>
  apply (rule map_atom_inj_eq_iff_eq)
  apply (simp add: inj_def lift_rel_exch4_eq fun_eq_iff)
  apply blast
  done


subsection \<open> Exchanged Unlifting \<close>

definition unlift_rel_exch4 (\<open>unlift'_rel\<^sub>\<ddagger>\<close>) where
  \<open>unlift_rel\<^sub>\<ddagger> r \<equiv> unlift_rel (r \<circ>\<^sub>2 \<ddagger>)\<close>

lemmas unlift_rel_exch4_eq = unlift_rel_exch4_def[simplified unlift_rel_def comp2_def]

lemma unlift_lift_rel_exch4_eq[simp]:
  \<open>unlift_rel\<^sub>\<ddagger> \<circ> lift_rel_exch4 = id\<close>
  by (simp add: unlift_rel_exch4_eq fun_eq_iff)


abbreviation unlift_comm_exch4 :: \<open>(('l \<times> 'l) \<times> ('s \<times> 's)) comm \<Rightarrow> ('l \<times> 's) comm\<close> where
  \<open>unlift_comm_exch4 \<equiv> map_atom unlift_rel_exch4\<close>

lemma unlift_comm_exch4_eq:
  \<open>unlift_comm_exch4 = map_atom (\<lambda>ar. ar \<circ>\<^sub>2 (\<ddagger> \<circ> \<Delta>))\<close>
  apply (clarsimp simp add: fun_eq_iff)
  apply (rule arg_cong2[where f=map_atom, OF _ refl])
  apply (simp add: unlift_rel_exch4_eq fun_eq_iff)
  done

lemmas unlift_comm_exch4_simps[simp] = map_atom.simps[of unlift_rel_exch4]

lemmas unlift_comm_exch4_rev_iff =
  map_atom_rev_iff[of unlift_rel_exch4]
  map_atom_rev_iff[of unlift_rel_exch4, THEN trans[OF eq_commute]]


subsection \<open> Exchanged Info-flow Properties \<close>

definition quasirefl_preserv_exch4 (\<open>quasirefl'_preserv\<^sub>\<ddagger>\<close>) where
  \<open>quasirefl_preserv\<^sub>\<ddagger> ar \<equiv> quasirefl_preserv (ar \<circ>\<^sub>2 \<ddagger>) \<circ> \<ddagger>\<close>

lemmas quasirefl_preserv_exch4_eq =
  quasirefl_preserv_exch4_def[simplified quasirefl_preserv_eq comp2_apply]


definition sym_preserv_exch4 (\<open>sym'_preserv\<^sub>\<ddagger>\<close>) where
  \<open>sym_preserv\<^sub>\<ddagger> ar \<equiv> sym_preserv (ar \<circ>\<^sub>2 \<ddagger>) \<circ> \<ddagger>\<close>

lemmas sym_preserv_exch4_eq =
  sym_preserv_exch4_def[simplified sym_preserv_eq]


definition quasireflcl_states_exch4 (\<open>quasireflcl'_states\<^sub>\<ddagger>\<close>) where
  \<open>quasireflcl_states\<^sub>\<ddagger> p \<equiv> quasireflcl_states (p \<circ> \<ddagger>) \<circ> \<ddagger>\<close>

lemmas quasireflcl_states_exch4_eq =
  quasireflcl_states_exch4_def[simplified quasireflcl_states_eq comp_apply]


definition symcl_states_exch4 (\<open>symcl'_states\<^sub>\<ddagger>\<close>) where
  \<open>symcl_states\<^sub>\<ddagger> p \<equiv> symcl_states (p \<circ> \<ddagger>) \<circ> \<ddagger>\<close>

lemmas symcl_states_exch4_eq =
  symcl_states_exch4_def[simplified symcl_states_def]


definition nonrevealing_exch4 (\<open>nonrevealing\<^sub>\<ddagger>\<close>) where
  \<open>nonrevealing\<^sub>\<ddagger> r \<equiv> nonrevealing (r \<circ>\<^sub>2 \<ddagger>) \<circ> \<ddagger>\<close>

lemmas nonrevealing_exch4_eq =
  nonrevealing_exch4_def[simplified nonrevealing_eq comp2_apply]


definition same_state_nonrevealing_exch4 (\<open>same'_state'_nonrevealing\<^sub>\<ddagger>\<close>) where
  \<open>same_state_nonrevealing\<^sub>\<ddagger> r \<equiv> \<top> \<le> nonrevealing (r \<circ>\<^sub>2 \<ddagger>) \<circ> \<Delta>\<close>

lemmas same_state_nonrevealing_exch4_eq =
  same_state_nonrevealing_exch4_def[simplified same_state_nonrevealing_def]


definition nondeclassifying_exch4 (\<open>nondeclassifying\<^sub>\<ddagger>\<close>) where
  \<open>nondeclassifying\<^sub>\<ddagger> r \<equiv> nondeclassifying (r \<circ>\<^sub>2 \<ddagger>) \<circ> \<ddagger>\<close>

lemmas nondeclassifying_exch4_eq =
  nondeclassifying_exch4_def[simplified nondeclassifying_def comp2_apply]

abbreviation declassifying_exch4 (\<open>declassifying\<^sub>\<ddagger>\<close>) where
  \<open>declassifying\<^sub>\<ddagger> \<equiv> - nondeclassifying\<^sub>\<ddagger>\<close>


definition enabled_split_exch4 (\<open>enabled'_split\<^sub>\<ddagger>\<close>) where
  \<open>enabled_split\<^sub>\<ddagger> r \<equiv> enabled_split (r \<circ>\<^sub>2 \<ddagger>) \<circ> \<ddagger>\<close>

lemmas enabled_split_exch4_eq =
  enabled_split_exch4_def[simplified enabled_split_def comp2_apply]


definition secure_rel_exch4 (\<open>secure'_rel\<^sub>\<ddagger>\<close>) where
  \<open>secure_rel\<^sub>\<ddagger> r \<equiv> secure_rel (r \<circ>\<^sub>2 \<ddagger>) \<circ> \<ddagger>\<close>

lemmas secure_rel_exch4_eq2 =
  secure_rel_exch4_def[simplified secure_rel_def]

lemma secure_rel_exch4_eq:
  \<open>secure_rel\<^sub>\<ddagger> a \<equiv> declassifying\<^sub>\<ddagger> a \<squnion> nonrevealing\<^sub>\<ddagger> a\<close>
  by (simp add: secure_rel_exch4_eq2 nondeclassifying_exch4_def
      nonrevealing_exch4_def enabled_split_exch4_def
      comp_inf_distrib comp_sup_distrib comp_neg_distrib)


subsubsection \<open> Lemmas \<close>

lemma quasireflcl_states_exch4_sec_agree_exch4_eq[simp]:
  \<open>quasireflcl_states\<^sub>\<ddagger> (\<bbbA>\<^sub>\<ddagger> f) = \<top>\<close>
  by (force simp add: quasireflcl_states_exch4_eq sec_agree_def)

lemma quasireflcl_states_exch4_neg_sec_agree_exch4_eq[simp]:
  \<open>quasireflcl_states\<^sub>\<ddagger> (- \<bbbA>\<^sub>\<ddagger> f) = \<bbbA>\<^sub>\<ddagger> f\<close>
  by (clarsimp simp add: quasireflcl_states_exch4_eq sec_agree_exch4_eq)

lemma sympp_states_exch4_neg_eq[simp]:
  \<open>symcl_states\<^sub>\<ddagger> (- p) = symcl_states\<^sub>\<ddagger> p\<close>
  by (force simp add: symcl_states_exch4_eq)

lemma sympp_states_exch4_sec_agree_exch4_eq[simp]:
  \<open>symcl_states\<^sub>\<ddagger> (\<bbbA>\<^sub>\<ddagger> f) = \<top>\<close>
  by (force simp add: symcl_states_exch4_eq sec_agree_def)

lemma secure_rel_exch4_bot_eq[simp]:
  \<open>secure_rel\<^sub>\<ddagger> \<bottom> = \<top>\<close>
  by (clarsimp simp add: fun_eq_iff secure_rel_exch4_def)

lemma secure_rel_exch4_eqrel_eq[simp]:
  \<open>secure_rel\<^sub>\<ddagger> (=) = \<top>\<close>
  by (clarsimp simp add: fun_eq_iff secure_rel_exch4_def)


end