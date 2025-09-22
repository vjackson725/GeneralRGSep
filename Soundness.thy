theory Soundness
  imports RGLogic
begin

(* TODO: move *)
definition
  \<open>res_conj_downcl p \<equiv> \<lambda>(x,y). \<exists>x'. x \<preceq> x' \<and> p (x', y)\<close>

definition
  \<open>res_conj_upcl p \<equiv> \<lambda>(x,y). \<exists>x'. x \<succeq> x' \<and> p (x', y)\<close>

lemma res_conj_downcl_mono:
  \<open>p \<le> q \<Longrightarrow> res_conj_downcl p \<le> res_conj_downcl q\<close>
  by (force simp add: res_conj_downcl_def)

lemma res_conj_downcl_inflationary:
  \<open>p \<le> res_conj_downcl p\<close>
  by (force simp add: res_conj_downcl_def)

lemma res_conj_downcl_idem[simp]:
  \<open>res_conj_downcl (res_conj_downcl p) = res_conj_downcl p\<close>
  using resource_preordering.trans
  by (simp add: res_conj_downcl_def fun_eq_iff, blast)


section \<open> Operational Semantics \<close>

type_synonym 's pconfig = \<open>'s \<times> 's comm\<close>

subsection \<open> Actions \<close>

datatype act = Tau | Vis

lemma act_not_eq_iff[simp]:
  \<open>\<alpha> \<noteq> Tau \<longleftrightarrow> \<alpha> = Vis\<close>
  \<open>\<alpha> \<noteq> Vis \<longleftrightarrow> \<alpha> = Tau\<close>
  by (meson act.distinct act.exhaust)+

lemma ex_act_eq[simp]:
  \<open>\<exists>\<alpha>. \<alpha> = Vis\<close>
  \<open>\<exists>\<alpha>. \<alpha> = Tau\<close>
  \<open>\<exists>\<alpha>. \<alpha> \<noteq> Vis\<close>
  \<open>\<exists>\<alpha>. \<alpha> \<noteq> Tau\<close>
  by blast+

lemma all_act_eq[simp]:
  \<open>(\<forall>\<alpha>. \<alpha> = Vis) \<longleftrightarrow> False\<close>
  \<open>(\<forall>\<alpha>. \<alpha> = Tau) \<longleftrightarrow> False\<close>
  \<open>(\<forall>\<alpha>. \<alpha> \<noteq> Vis) \<longleftrightarrow> False\<close>
  \<open>(\<forall>\<alpha>. \<alpha> \<noteq> Tau) \<longleftrightarrow> False\<close>
  by blast+

lemma all_act_iff:
  \<open>(\<forall>\<alpha>. p \<alpha>) \<longleftrightarrow> p Tau \<and> p Vis\<close>
  by (metis act_not_eq_iff(1))

lemma ex_act_iff:
  \<open>(\<exists>\<alpha>. p \<alpha>) \<longleftrightarrow> p Tau \<or> p Vis\<close>
  by (metis act_not_eq_iff(2))


subsection \<open> Operational semantics steps \<close>

fun opstep :: \<open>act \<Rightarrow> 's pconfig \<Rightarrow> 's pconfig \<Rightarrow> bool\<close> where
  \<open>opstep \<alpha> (s, Skip) sc' \<longleftrightarrow> False\<close>
| \<open>opstep \<alpha> (s, ca ;; cb) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    (\<exists>s' ca'. opstep \<alpha> (s, ca) (s', ca') \<and> sc' = (s', ca' ;; cb))\<close>
| \<open>opstep \<alpha> (s, ca \<^bold>\<sqinter> cb) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> sc' = (s, ca) \<or>
    \<alpha> = Tau \<and> sc' = (s, cb)\<close>
| \<open>opstep \<alpha> (s, ca \<^bold>\<box> cb) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    \<alpha> = Tau \<and> cb = Skip \<and> sc' = (s, ca) \<or>
    \<alpha> = Tau \<and> (\<exists>s' ca'. sc' = (s', ca' \<^bold>\<box> cb) \<and> opstep Tau (s, ca) (s', ca')) \<or>
    \<alpha> = Tau \<and> (\<exists>s' cb'. sc' = (s', ca \<^bold>\<box> cb') \<and> opstep Tau (s, cb) (s', cb')) \<or>
    \<alpha> \<noteq> Tau \<and> opstep \<alpha> (s, ca) sc' \<or>
    \<alpha> \<noteq> Tau \<and> opstep \<alpha> (s, cb) sc'\<close>
| \<open>opstep \<alpha> (s, ca \<parallel> cb) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> ca = Skip \<and> cb = Skip \<and> sc' = (s, Skip) \<or>
    (\<exists>s' ca'. opstep \<alpha> (s, ca) (s', ca') \<and> sc' = (s', ca' \<parallel> cb)) \<or>
    (\<exists>s' cb'. opstep \<alpha> (s, cb) (s', cb') \<and> sc' = (s', ca \<parallel> cb'))\<close>
| \<open>opstep \<alpha> (s, DO c OD) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> (\<forall>\<alpha>' sc'. \<not> opstep \<alpha>' (s, c) sc') \<and> sc' = (s, Skip) \<or>
    (\<exists>s' c'. opstep \<alpha> (s, c) (s', c') \<and> sc' = (s', c' ;; DO c OD))\<close>
| \<open>opstep \<alpha> (s, Atomic ar) sc' \<longleftrightarrow>
    \<alpha> = Vis \<and> ar s (fst sc') \<and> snd sc' = Skip\<close>

lemmas opstep_induct =
  opstep.induct[case_names Skip Seq Indet Endet Par DoLoop Atom]


paragraph \<open> Pretty operational semantics \<close>

abbreviation pretty_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>sc \<midarrow>\<alpha>\<rightarrow> msc' \<equiv> opstep \<alpha> sc msc'\<close>

abbreviation pretty_no_opstep :: \<open>_ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>'/\<rightarrow>\<close> [60] 60) where
  \<open>sc \<midarrow>/\<rightarrow> \<equiv> \<forall>\<alpha> sc'. \<not> opstep \<alpha> sc sc'\<close>


subsection \<open> Lemmas about opstep \<close>

lemma opstep_tau_preserves_heap:
  assumes \<open>s \<midarrow>Tau\<rightarrow> s'\<close>
  shows \<open>fst s' = fst s\<close>
proof -
  { fix \<alpha>
    have \<open>s \<midarrow>\<alpha>\<rightarrow> s' \<Longrightarrow> \<alpha> = Tau \<Longrightarrow> fst s' = fst s\<close>
      by (induct \<alpha> s s' rule: opstep.induct) (force split: if_splits)+
  }
  then show ?thesis
    using assms by force
qed

lemma vis_step_impl_atom:
  assumes
    \<open>(s, c) \<midarrow>Vis\<rightarrow> (s', c')\<close>
  shows
    \<open>\<exists>ar. ar \<in># head_atoms c \<and> ar s s'\<close>
proof -
  { fix \<alpha> sc sc'
    have
      \<open>sc \<midarrow>\<alpha>\<rightarrow> sc' \<Longrightarrow>
        sc = (s, c) \<Longrightarrow>
        sc' = (s', c') \<Longrightarrow>
        \<alpha> = Vis \<Longrightarrow>
        \<exists>ar. ar \<in># head_atoms c \<and> ar s s'\<close>
      by (induct \<alpha> sc sc' arbitrary: c s s' c' rule: opstep.induct)
        fastforce+
  }
  then show ?thesis
    using assms
    by blast
qed

lemma opstep_act_cases:
  \<open>s \<midarrow>\<alpha>\<rightarrow> s' \<Longrightarrow>
    (\<alpha> = Tau \<Longrightarrow> s \<midarrow>Tau\<rightarrow> s' \<Longrightarrow> fst s' = (fst s) \<Longrightarrow> P) \<Longrightarrow>
    (\<alpha> = Vis \<Longrightarrow> s \<midarrow>Vis\<rightarrow> s' \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  by (metis (full_types) act.exhaust opstep_tau_preserves_heap)

lemma all_atom_comm_opstep:
  assumes
    \<open>opstep \<alpha> (h, c) (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows
    \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    assume \<open>opstep \<alpha> s s'\<close>
      and \<open>all_atom_comm p (snd s)\<close>
    then have \<open>all_atom_comm p (snd s')\<close>
      by (induct \<alpha> s s' rule: opstep.induct) (force split: if_splits)+
  }
  then show ?thesis
    using assms
    by (metis snd_conv)
qed

lemmas all_atom_comm_opstepD =
  all_atom_comm_opstep[rotated]


subsubsection \<open> adding parallel \<close>

lemma opstep_parallel_leftD:
  \<open>s \<midarrow>\<alpha>\<rightarrow> s' \<Longrightarrow> (fst s, snd s \<parallel> cy) \<midarrow>\<alpha>\<rightarrow> (fst s', snd s' \<parallel> cy)\<close>
  by simp

lemma opstep_parallel_rightD:
  \<open>s \<midarrow>\<alpha>\<rightarrow> s' \<Longrightarrow> (fst s, cx \<parallel> snd s) \<midarrow>\<alpha>\<rightarrow> (fst s', cx \<parallel> snd s')\<close>
  by simp


subsubsection \<open> iteraction with all_atom_comm \<close>

lemma opstep_preserves_all_atom_comm:
  assumes
    \<open>opstep \<alpha> (h, c) (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    have \<open>opstep \<alpha> s s' \<Longrightarrow> all_atom_comm p (snd s) \<Longrightarrow> all_atom_comm p (snd s')\<close>
      by (induct \<alpha> s s' arbitrary: h' rule: opstep.induct)
        (force split: if_splits)+
  }
  then show ?thesis
    using assms
    by (metis snd_conv)
qed

lemmas rev_opstep_preserves_all_atom_comm = opstep_preserves_all_atom_comm[rotated]


subsection \<open> Opstep rules for defined programs \<close>

paragraph \<open> Assert \<close>

lemma opstep_assert_iff[simp]:
  \<open>opstep \<alpha> (s, Assert p) sc' \<longleftrightarrow>
    \<alpha> = Vis \<and>
    snd sc' = Skip \<and>
    (snd (snd s) = Running \<and>
      fst (fst sc') = fst s \<and>
      fst (snd (fst sc')) = fst (snd s) \<and>
      (p (fst s, fst (snd s)) \<and> snd (snd (fst sc')) = Running \<or>
        \<not> p (fst s, fst (snd s)) \<and> snd (snd (fst sc')) = Failed) \<or>
      snd (snd s) = Failed \<and> s = fst sc')\<close>
  by (force simp add: Assert_def case_prod_beta)


paragraph \<open> Await \<close>

lemma opstep_await_iff[simp]:
  \<open>opstep \<alpha> (s, Await p) sc' \<longleftrightarrow>
    \<alpha> = Vis \<and> p s \<and> sc' = (s, Skip)\<close>
  by (cases sc', force simp add: Await_def)


paragraph \<open> IfThenElse \<close>

lemma opstep_IfThenElse_iff[simp]:
  \<open>opstep \<alpha> (s, IfThenElse p ct cf) sc' \<longleftrightarrow>
    \<alpha> = Vis \<and>
    (p s \<and> sc' = (s, Skip ;; ct) \<or>
      \<not> p s \<and> sc' = (s, Skip ;; cf))\<close>
  by (cases sc', force simp add: IfThenElse_def Await_def)

lemma opstep_WhileLoop_iff[simp]:
  \<open>opstep \<alpha> (h, WhileLoop p c) s' \<longleftrightarrow>
    \<alpha> \<noteq> Tau \<and> p h \<and> s' = (h, (Skip ;; c) ;; DO Await p ;; c OD) \<or>
    \<alpha> = Tau \<and> \<not> p h \<and> s' = (h, Skip)\<close>
  by (force simp add: WhileLoop_def Await_def pre_state_def)


section \<open> Safe \<close>

text \<open>
  The inductive predicate \<open>safe\<close> defines a tree semantics of our program \<open>c\<close>.
  It considers all executions from \<open>s\<close>, which include environment steps specified by \<open>R\<close>,
  and local \<open>opsteps\<close> from the current state (for which the state is framed by some frame in \<open>F\<close>).
    It enforces that all reachable states (from the view of the current process) must obey the
  state invariant \<open>I\<close> and all local steps must fulfil the guarantee condition \<open>G\<close>. 
  In addition, if the execution terminates, the final state must uphold the postcondition \<open>q\<close>.
\<close>
inductive safe
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow>
      ('l::pre_perm_alg \<times> 's) comm \<Rightarrow>
      'l \<times> 's \<Rightarrow>
      bool\<close>
  for R F G I q
  where safeI[intro]:
  \<open>\<comment> \<open> If the command is Skip, the postcondition is established.
        Note: this semantics represents termination by infinite final stuttering. \<close>
    (c = Skip \<longrightarrow> q s) \<Longrightarrow>
    \<comment> \<open> the current state obeys the state invariant \<close>
    I s \<Longrightarrow>
    \<comment> \<open> rely steps are safe \<close>
    (\<And>n' ss'. n = Suc n' \<Longrightarrow> R (snd s) ss' \<Longrightarrow> safe R F G I q n' c (fst s, ss')) \<Longrightarrow>
    \<comment> \<open> closed under opsteps \<close>
    (\<And>n' \<alpha> s' c'.
      n = Suc n' \<Longrightarrow>
      (s, c) \<midarrow>\<alpha>\<rightarrow> (s', c') \<Longrightarrow>
      (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) (snd s')) \<and>
        (\<alpha> = Tau \<longrightarrow> fst s' = fst s) \<and>
        safe R F G I q n' c' s') \<Longrightarrow>
    \<comment> \<open> closed under framed opsteps \<close>
    (\<And>n' fs \<alpha> lfs' ss' c'.
      n = Suc n' \<Longrightarrow>
      ((fst s + fs, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((lfs', ss'), c') \<Longrightarrow>
      fst s ## fs \<Longrightarrow>
      F (fs, snd s) \<Longrightarrow>
      \<comment> \<open> Non-tau steps establish the guarantee. \<close>
      (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) ss') \<and>
      \<comment> \<open> Note the existential! We only guarantee \<^emph>\<open>one\<close> such unframed state is safe.
           This is only relevant for non-cancellative frame, in which case the states in question
           are a verification fiction anyway, so this is reasonable. \<close>
      (\<exists>ls'.
        ls' ## fs \<and>  \<comment> \<open> note we require preservation of separation from the \<^emph>\<open>whole\<close> frame. \<close>
        lfs' = ls' + fs \<and>
        (\<alpha> = Tau \<longrightarrow> ls' = fst s) \<and> \<comment> \<open> Tau moves are not allowed to change the fictive state! \<close>
        safe R F G I q n' c' (ls', ss'))) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe R F G I q n c s\<close>


subsection \<open> Proofs about safe \<close>

inductive_cases safe_zeroE[elim!]: \<open>safe R F G I q 0 c s\<close>
inductive_cases safe_sucE[elim]: \<open>safe R F G I q (Suc n) c s\<close>

lemma safe_then_state_inv:
  assumes \<open>safe R F G I q n c s\<close>
  shows \<open>I s\<close>
  using assms
  by (induct rule: safe.inducts) blast+

lemma safe_then_postcond:
  assumes \<open>safe R F G I q n c s\<close>
  shows \<open>c = Skip \<longrightarrow> q s\<close>
  using assms
  by (induct rule: safe.inducts) blast+


lemma safe_nil_iff[simp]:
  \<open>safe R F G I q 0 c s \<longleftrightarrow> (c = Skip \<longrightarrow> q s) \<and> I s\<close>
  by blast

lemma safe_suc_iff:
  \<open>safe R F G I q (Suc n) c s \<longleftrightarrow>
    (c = Skip \<longrightarrow> q s) \<and>
    I s \<and>
    (\<forall>ss'. R (snd s) ss' \<longrightarrow> safe R F G I q n c (fst s, ss')) \<and>
    (\<forall>\<alpha> s' c'.
      (s, c) \<midarrow>\<alpha>\<rightarrow> (s', c') \<longrightarrow>
      (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) (snd s')) \<and>
        (\<alpha> = Tau \<longrightarrow> fst s' = fst s) \<and>
        safe R F G I q n c' s') \<and>
    (\<forall>\<alpha> lfs' ss' fs c'.
      ((fst s + fs, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((lfs', ss'), c') \<longrightarrow>
      fst s ## fs \<longrightarrow>
      F (fs, snd s) \<longrightarrow>
      (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) ss') \<and>
      (\<exists>ls'.
        ls' ## fs \<and>
        lfs' = ls' + fs \<and>
        (\<alpha> = Tau \<longrightarrow> ls' = fst s) \<and>
        safe R F G I q n c' (ls', ss')))\<close>
  apply (rule iffI)
   apply (elim safe_sucE; simp; fail)
  apply (rule safeI; force)
  done

lemma safe_sucD:
  \<open>safe R F G I q (Suc n) c s \<Longrightarrow> R ss ss' \<Longrightarrow> ss = snd s \<Longrightarrow> safe R F G I q n c (fst s, ss')\<close>
  \<open>safe R F G I q (Suc n) c s \<Longrightarrow>
    (s, c) \<midarrow>\<alpha>\<rightarrow> (s', c') \<Longrightarrow>
    (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) (snd s')) \<and>
      (\<alpha> = Tau \<longrightarrow> fst s' = fst s) \<and>
      safe R F G I q n c' s'\<close>
  \<open>safe R F G I q (Suc n) c s \<Longrightarrow>
    ((fst s + fs, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((slf', ss'), c') \<Longrightarrow>
    fst s ## fs \<Longrightarrow>
    F (fs, snd s) \<Longrightarrow>
    (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) ss') \<and>
    (\<exists>sl'.
      sl' ## fs \<and>
      slf' = sl' + fs \<and>
      (\<alpha> = Tau \<longrightarrow> sl' = fst s) \<and>
      safe R F G I q n c' (sl', ss'))\<close>
  by (erule safe_sucE, (simp; fail))+


subsubsection \<open> Monotonicity of safe \<close>

lemma safe_monoD:
  \<open>safe R F G I q n c s \<Longrightarrow>
    R' \<le> R \<Longrightarrow>
    F' \<le> F \<Longrightarrow>
    G \<le> G' \<Longrightarrow>
    I \<le> I' \<Longrightarrow>
    q \<le> q' \<Longrightarrow>
    m \<le> n \<Longrightarrow>
    safe R' F' G' I' q' m c s\<close>
  apply (induct arbitrary: m rule: safe.induct)
  apply (rule safeI)
      apply (metis predicate1D)
     apply (metis predicate1D)
    apply (clarsimp simp add: Suc_leq_iff)
    apply (metis predicate2D)
   apply (clarsimp simp add: Suc_leq_iff)
   apply (metis predicate2D)
  apply (clarsimp simp add: Suc_leq_iff)
  apply (drule meta_spec2, drule meta_spec2, drule meta_spec2, drule meta_spec,
      drule meta_mp, rule refl, drule meta_mp, assumption)
  apply (drule meta_mp, blast)
  apply (metis le_boolD le_funE)
  done

lemmas safe_mono = safe_monoD[rotated]

lemmas safe_mono_stepsD = safe_monoD[OF _ order.refl order.refl order.refl order.refl order.refl]
lemmas safe_mono_steps = safe_mono_stepsD[rotated]

lemmas safe_mono_invD = safe_monoD[OF _ order.refl order.refl order.refl _ order.refl order.refl]
lemmas safe_mono_inv = safe_mono_invD[rotated]

lemmas safe_mono_postD = safe_monoD[OF _ order.refl order.refl order.refl order.refl _ order.refl]
lemmas safe_mono_post = safe_mono_postD[rotated]

lemmas safe_mono_guarD = safe_monoD[OF _ order.refl order.refl _ order.refl order.refl order.refl]
lemmas safe_mono_guar = safe_mono_guarD[rotated]

lemmas safe_mono_frameD = safe_monoD[OF _ order.refl _ order.refl order.refl order.refl order.refl]
lemmas safe_mono_frame = safe_mono_frameD[rotated]


lemma safe_step_SucD:
  \<open>safe R F G I q (Suc n) c s \<Longrightarrow> safe R F G I q n c s\<close>
  by (metis safe_mono_stepsD le_add2 plus_1_eq_Suc)


subsection \<open> Safety of Skip \<close>

lemma safe_skip_iff:
  \<open>safe R F G I q n Skip s \<longleftrightarrow>
    (\<exists>sl ss. s = (sl, ss) \<and> (\<forall>k\<le>n. \<forall>ss'. (R^^k) ss ss' \<longrightarrow> q (sl, ss') \<and> I (sl, ss')))\<close>
  apply (induct n arbitrary: s)
   apply (simp; fail)
  apply (rule iffI)
   apply (erule safe_sucE)
   apply (clarsimp simp add: le_Suc_iff0)
   apply (metis relpowp_Suc_D2')
  apply (clarsimp simp add: safe_suc_iff le_Suc_iff0 all_conj_distrib imp_ex_conjL)
  apply (metis OO_def relpowp_commute)
  done

lemma safe_skip_stable_iff:
  assumes
    \<open>sswa R I \<le> I\<close>
    \<open>sswa R q \<le> q\<close>
  shows
    \<open>safe R F G I q n Skip s \<longleftrightarrow> q s \<and> I s\<close>
  using assms
  apply (simp add: safe_skip_iff sp_def le_fun_def imp_ex_conjL)
  apply (metis bot_nat_0.extremum relpowp_0_I rtranclp_power split_pairs2)
  done

lemma safe_skip':
  \<open>wssa R q s \<Longrightarrow> wssa R I s \<Longrightarrow> safe R F G I q n Skip s\<close>
  apply (induct n arbitrary: s)
   apply force
  apply (case_tac s)
  apply clarsimp
  apply (rule safeI)
      apply force
     apply force
    apply (simp add: wssa_step; fail)
   apply force
  apply force
  done

lemma safe_skip:
  \<open>p s \<Longrightarrow> p \<le> wssa R q \<Longrightarrow> p \<le> wssa R I \<Longrightarrow> safe R F G I q n Skip s\<close>
  apply (rule safe_monoD[OF _ order.refl order.refl order.refl order.refl order.refl order.refl])
  apply (rule safe_skip'[where q=\<open>q\<close>])
   apply blast
  apply blast
  done


subsection \<open> Safety of frame \<close>

lemma safe_from_frame_spec_downcl:
  \<open>safe R (res_conj_downcl F) G I q n c s \<Longrightarrow>
    safe R F G I q n c s\<close>
proof (induct rule: safe.inducts)
  case (safeI c s n)
  show ?case
    apply -
    apply (rule safe.safeI)
      (* subgoal: post-condition *)
        apply (rule safeI.hyps(1))
      (* subgoal: state invariant *)
       apply (rule safeI.hyps(2))
      (* subgoal: rely step *)
      apply (rule safeI.hyps(4); fast)
      (* subgoal: opstep *)
     apply (frule(1) safeI.hyps(5), blast)
      (* subgoal: framed opstep *)
    apply (rename_tac fF)
    apply (frule(2) safeI.hyps(6))
     apply (clarsimp simp add: res_conj_downcl_def)
     apply blast
    apply blast
    done
qed

text \<open>
  The frame specification is 'chunky', in that is represents the frames that could possibly
  come from other processes. These do \<^emph>\<open>not\<close> have to be downwards closed. The frame rule is,
  essentially, constructing a 'virtual' process.
    We must assume that the frame specification of the assumption includes not only the sepconj of
  the two elements, but also the frame spec. and frame predicate without any separating conjunction,
  i.e. \<open>F \<^emph>\<and> F' \<squnion> F'\<close>.
\<close>
lemma safe_frame':
  assumes ni_assms:
    \<open>sswa (R \<squnion> G) F' \<le> F'\<close>
  shows
  \<open>safe R (F \<^emph>\<and> F' \<squnion> F \<squnion> F') G I q n c s \<Longrightarrow>
    fst s ## fs \<Longrightarrow>
    F' (fs, snd s) \<Longrightarrow>
    safe R F G (I \<^emph>\<and> F') (q \<^emph>\<and> F') n c (fst s + fs, snd s)\<close>
proof (induct arbitrary: fs rule: safe.induct)
  case (safeI c s n)

  note hyps = safeI.hyps[simplified safeI.prems(1)[simplified] fst_conv snd_conv]

  show ?case
    using safeI.prems(1-2) hyps(1-2)
    apply -
    apply (rule safe.safeI)
      (* subgoal: skip *)
        apply (force simp add: sepconj_conj_def simp del: sup_apply)
      (* subgoal: stateset *)
       apply (metis sepconj_conjI surjective_pairing)
      (* subgoal: rely step *)
      apply (simp del: sup_apply top_apply inf_apply)
      apply (rule hyps(4), fast, fast, fast)
      apply (cut_tac ni_assms(1))
      apply (meson predicate1D sswa_step sswa_trivial sup2I1; fail)
      (* subgoal: opstep *)
     apply (clarsimp simp del: sup_apply top_apply inf_apply)
     apply (drule(2) hyps(6), force)
     apply (clarsimp simp del: sup_apply top_apply inf_apply)
     apply (drule spec, drule mp[of \<open>_ ## _\<close>], assumption)
     apply (drule mp[of \<open>F' _\<close>])
      apply (metis (no_types, lifting) fst_conv ni_assms(1) opstep_act_cases order_antisym snd_conv
        sswa_step sswa_weaker sup2I2)
     apply fast
      (* subgoal: framed opstep *)
    apply (rename_tac n' fsx \<alpha> lfs' ss' c')
    apply (clarsimp simp add: partial_add_assoc2[of \<open>fst s\<close> fs] simp del: sup_apply top_apply)
    apply (frule hyps(6)[rotated 1])
       apply (metis disjoint_add_swap_lr)
      apply (simp add: sepconj_conj_apply)
      apply (metis disjoint_add_leftR disjoint_sym partial_add_commute)
     apply (simp add: disjoint_add_swap_lr; fail)
    apply (clarsimp simp del: top_apply sup_apply inf_apply)
    apply (erule opstep_act_cases)
     apply (simp add: disjoint_preservation2 partial_add_assoc2; fail)
    apply (rule_tac x=\<open>ls' + fs\<close> in exI)
    apply (intro conjI)
       apply (metis disjoint_add_leftR disjoint_add_swap_rl)
      apply (metis disjoint_add_leftR partial_add_assoc3)
     apply blast
    apply (drule_tac x=fs in spec, drule mp, rule disjoint_add_rightL[rotated], assumption)
     apply (metis disjoint_add_leftR)
    apply (drule mp[of \<open>F' _\<close>])
     apply (metis (full_types) ni_assms(1) predicate1D sswa_step sswa_trivial sup2I2)
    apply fast
    done
qed

lemma safe_frame:
  \<open>safe R (F \<^emph>\<and> F' \<squnion> F \<squnion> F') G I q n c s \<Longrightarrow>
    fst s ## fs \<Longrightarrow>
    s' = (fst s + fs, snd s) \<Longrightarrow>
    sswa (R \<squnion> G) F' \<le> F' \<Longrightarrow>
    F' (fs, snd s) \<Longrightarrow>
    safe R F G (I \<^emph>\<and> F') (q \<^emph>\<and> F') n c s'\<close>
  by (simp add: safe_frame')


subsection \<open> Safety of Atomic \<close>

lemma safe_atom':
  \<open>sp ar (sswa R p) \<le> q \<Longrightarrow>
    \<forall>f\<le>F. sp ar (sswa R p \<^emph>\<and> f) \<le> q \<^emph>\<and> f \<Longrightarrow>
    sswa R p s \<Longrightarrow>
    safe R F
      (rel_image snd (rel_liftL (sswa R p \<squnion> sswa R p \<^emph>\<and> F) \<sqinter> ar)) \<comment> \<open> G \<close>
      (sswa R p \<squnion> sswa R q) \<comment> \<open> I \<close>
      (sswa R q) \<comment> \<open> q \<close>
      n \<langle>ar\<rangle> s\<close>
proof (induct n arbitrary: s)
  case (Suc n)
  note ih = Suc.hyps[simplified fst_conv snd_conv]
  show ?case
    using Suc.prems
    apply -
    apply (cases s)
    apply (rename_tac sl ss)
    apply (clarsimp simp del: sup_apply inf_apply top_apply rel_lift_apply rel_image_apply)
    apply (rule safeI)
      (* subgoal: termination *)
       apply force
      (* subgoal: state inv *)
      apply force
      (* subgoal: rely *)
      apply (clarsimp simp del: sup_apply inf_apply rel_lift_apply top_apply rel_image_apply)
      apply (simp add: ih sswa_step; fail)
      (* subgoal: local opstep *)
     apply (rule conjI[OF _ conjI])
      (* subsubgoal: guarantee *)
       apply force
      (* subsubgoal: tau *)
      apply force
      (* subsubgoal: safe *)
     apply (clarsimp simp del: sup_apply inf_apply rel_lift_apply top_apply)
     apply (simp add: safe_skip_stable_iff sp_sup, blast)
      (* subgoal: local framed opstep *)
    apply (rule conjI)
      (* subsubgoal: guarantee *)
     apply (simp, metis disjoint_sym_iff partial_add_commute sepconj_conj_revI)
      (* subsubgoal: safety after opstep *)
    apply (clarsimp simp del: sup_apply inf_apply top_apply rel_lift_apply
        simp add: safe_skip_stable_iff sp_sup)
    apply (frule spec[of _ \<open>(=) _\<close>], frule mp, blast)
    apply (clarsimp simp add: sp_def[of ar] le_fun_def imp_ex_conjL sepconj_conj_def)
    apply fast
    done
qed simp

lemma safe_atom:
  \<open>sp ar (sswa R p) \<le> q \<Longrightarrow>
    \<forall>f\<le>F. sp ar (sswa R p \<^emph>\<and> f) \<le> q \<^emph>\<and> f \<Longrightarrow>
    rel_image snd (rel_liftL (sswa R p \<squnion> sswa R p \<^emph>\<and> F) \<sqinter> ar) \<le> G \<Longrightarrow>
    wssa R p s \<Longrightarrow>
    sswa R p \<le> I \<Longrightarrow>
    sswa R q \<le> I \<Longrightarrow>
    sswa R q \<le> q' \<Longrightarrow>
    safe R F G I q' n \<langle>ar\<rangle> s\<close>
  by (rule safe_monoD[OF safe_atom' order.refl order.refl _ _ _ order.refl])
    blast+


subsection \<open> Safety of Sequencing \<close>

lemma safe_seq_assoc_left:
  \<open>safe R F G I q n c s \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe R F G I q n ((c1 ;; c2) ;; c3) s\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
  apply (rule safeI)
      apply blast
     apply blast
    apply blast
   apply (simp, elim disjE conjE exE)
    apply force
   apply metis
  apply (simp, elim disjE conjE exE)
   apply force
  apply metis
  done

lemma safe_seq_assoc_right:
  \<open>safe R F G I q n c s \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    safe R F G I q n (c1 ;; c2 ;; c3) s\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
  apply (rule safeI)
      apply blast
     apply blast
    apply blast
   apply (simp, elim disjE conjE exE)
    apply force
   apply metis
  apply (simp, elim disjE conjE exE)
   apply force
  apply metis
  done

lemma safe_seq':
  \<open>safe R F Ga Ia q n ca s \<Longrightarrow>
    \<forall>s'. q s' \<longrightarrow> safe R F Gb Ib q' n cb s' \<Longrightarrow>
    safe R F (Ga \<squnion> Gb) (Ia \<squnion> Ib) q' n (ca ;; cb) s\<close>
proof (induct arbitrary: cb q' rule: safe.inducts)
  case (safeI c s n)
  show ?case
    using safeI.hyps(1-2)
    apply -
    apply (rule safe.safeI)
      (* subgoal: skip *)
        apply fast
      (* subgoal: stateset *)
       apply fast
      (* subgoal: rely *)
      apply (metis safeI.hyps(4) safeI.prems safe_step_SucD)
      (* subgoal: local opstep *)
     apply (clarsimp simp del: sup_apply simp add: le_Suc_iff0 all_conj_distrib imp_ex_conjL)
     apply (elim disjE conjE exE)
      apply simp
      apply (metis safeI.prems safe_mono_guarD safe_mono_invD safe_step_SucD fst_conv
        sup.cobounded2)
     apply simp
     apply (metis safeI.hyps(5) safeI.prems safe_step_SucD act.distinct(1) fst_conv snd_conv)
      (* subgoal: local framed opstep *)
     apply (clarsimp simp del: sup_apply)
    apply (elim disjE conjE exE)
     apply (metis safeI.prems safe_mono_guarD safe_mono_invD safe_step_SucD act.distinct(1)
        sup.cobounded2 surjective_pairing)
    apply (frule(3) safeI.hyps(6))
    apply (clarsimp simp del: sup_apply)
    apply (metis safeI.prems safe_step_SucD sup2I1)
    done
qed

lemma safe_seq:
  \<open>safe R F Ga Ia q n ca s \<Longrightarrow>
    \<forall>s'. q s' \<longrightarrow> safe R F Gb Ib q' n cb s' \<Longrightarrow>
    Ga \<le> G \<Longrightarrow>
    Gb \<le> G \<Longrightarrow>
    Ia \<le> I \<Longrightarrow>
    Ib \<le> I \<Longrightarrow>
    safe R F G I q' n (ca ;; cb) s\<close>
  by (rule safe_monoD[OF safe_seq' order.refl order.refl _ _ order.refl order.refl])
    blast+


subsection \<open> Safety of Iter \<close>

lemma safe_iter':
  \<open>\<forall>s'. wssa R i s' \<longrightarrow> safe R F G I (wssa R i) n c s' \<Longrightarrow>
    wssa R i s \<Longrightarrow>
    safe R F G I (wssa R i) n (Iter c) s\<close>
proof (induct n arbitrary: i s)
  case (Suc n)
  have safe_n_c:
    \<open>\<forall>s'. wssa R i s' \<longrightarrow> safe R F G I (wssa R i) n c s'\<close>
    using Suc.prems(1) by (meson safe_step_SucD)
  note safe_ih = Suc.hyps[OF safe_n_c]

  have safe_suc_c:
    \<open>\<And>s'. wssa R i s' \<Longrightarrow> safe R F G I (wssa R i) (Suc n) c s'\<close>
    using Suc.prems(1) by blast
  note safe_suc_cD = safe_sucD[OF safe_suc_c]

  show ?case
    using Suc.prems(1-2)
    apply -
    apply (rule safe.safeI)
      (* subgoal: skip *)
        apply blast
      (* subgoal: stateset *)
       apply blast
      (* subgoal: rely *)
      apply (metis Suc_inject surjective_pairing safe_ih wssa_step)
      (* subgoal: opstep *)
     apply clarsimp
     apply (elim disjE conjE exE)
      apply (clarsimp simp add: safe_skip_iff)
      apply (metis rtranclp_idemp rtranclp_power safe_then_state_inv wssa_stepD)
     apply (intro conjI)
       apply (metis eq_snd_iff safe_sucE)
      apply (metis opstep_tau_preserves_heap prod_eq_decompose(2))
     apply clarsimp
     apply (frule(1) safe_suc_cD(2))
     apply (rule safe_seq[OF _ allI[OF impI[OF safe_ih]]]; blast)
      (* subgoal: framed opstep *)
    apply (simp add: le_fun_def del: split_paired_All)
    apply (elim disjE conjE exE)
     apply (clarsimp simp add: safe_skip_iff)
     apply (metis (no_types) relpowp_imp_rtranclp rtranclp_idemp safe_sucE split_pairs wssa_step)
    apply (rule conjI, fast)
    apply (frule(3) safe_suc_cD(3))
    apply clarsimp
    apply (rule_tac x=sl' in exI)
    apply (intro conjI)
       apply blast
      apply blast
     apply blast
    apply (rule safe_seq[OF _ allI[OF impI[OF safe_ih]]]; blast)
    done
qed force

lemma safe_iter:
  \<open>\<forall>s'. wssa R i s' \<longrightarrow> safe R F G I (wssa R i) n c s' \<Longrightarrow>
    wssa R i s \<Longrightarrow>
    wssa R i \<le> q' \<Longrightarrow>
    safe R F G I q' n (Iter c) s\<close>
  using safe_iter'
  by (metis (no_types, opaque_lifting) safe_mono_postD)


subsubsection \<open> Safety of internal nondeterminism \<close>

lemma safe_indet':
    \<open>safe R F Ga Ia qa n ca s \<Longrightarrow>
      safe R F Gb Ib qb n cb s \<Longrightarrow>
      safe R F (Ga \<squnion> Gb) (Ia \<squnion> Ib) (qa \<squnion> qb) n (ca \<^bold>\<sqinter> cb) s\<close>
proof (induct n arbitrary: ca cb s)
  case (Suc n)
  show ?case
    using Suc.prems
    apply -
    apply (rule safeI)
      (* subgoal: rely *)
        apply blast
      (* subgoal: state inv *)
       apply blast
      (* subgoal: rely *)
      apply (metis Suc.hyps nat.inject safe_sucD(1))
      (* subgoal: opstep *)
     apply (clarsimp simp add: conj_disj_distribL[symmetric] simp del: sup_apply)
    apply (meson Suc_n_not_le_n order.refl inf_sup_ord(3,4) linorder_le_cases safe_mono; fail)
      (* subgoal: framed opstep *)
    apply (clarsimp simp add: conj_disj_distribL[symmetric] simp del: sup_apply)
    apply (meson Suc_n_not_le_n order.refl inf_sup_ord(3,4) linorder_le_cases safe_mono; fail)
    done
qed blast

lemma safe_indet:
  \<open>safe R F Ga Ia qa n ca s \<Longrightarrow>
      safe R F Gb Ib qb n cb s \<Longrightarrow>
      Ia \<le> I \<Longrightarrow>
      Ib \<le> I \<Longrightarrow>
      Ga \<le> G \<Longrightarrow>
      Gb \<le> G \<Longrightarrow>
      qa \<le> q \<Longrightarrow>
      qb \<le> q \<Longrightarrow>
      safe R F G I q n (ca \<^bold>\<sqinter> cb) s\<close>
  by (rule safe_monoD[OF safe_indet' order.refl order.refl _ _ _ order.refl])
    blast+


subsubsection \<open> Safety of external nondeterminism \<close>

lemma safe_endet':
  \<open>safe R F Ga Ia qa n ca s \<Longrightarrow>
    safe R F Gb Ib qb n cb s \<Longrightarrow>
    safe R F (Ga \<squnion> Gb) (Ia \<squnion> Ib) (qa \<squnion> qb) n (ca \<^bold>\<box> cb) s\<close>
proof (induct n arbitrary: ca cb s)
  case (Suc n)
  show ?case
    using Suc.prems
    apply -
    apply (rule safeI)
      (* subgoal: skip *)
        apply blast
      (* subgoal: state inv. *)
       apply blast
      (* subgoal: rely *)
      apply (metis Suc.hyps nat.inject safe_sucD(1))
      (* subgoal: opstep *)
     apply (simp del: sup_apply)
     apply (intro conjI)
       apply (metis act.distinct(1) safe_sucD(2) sup2CI)
      apply (metis safe_sucE)
      (** ih *)
     apply (simp only: disj.assoc[symmetric, of _ _ \<open>_ \<or> _\<close>])
     apply (erule disjE, erule disjE)
       apply (meson Suc_n_not_le_n order.refl nat_le_linear safe_mono sup_ge1 sup_ge2; fail)
      apply (metis (no_types, lifting) Suc.hyps opstep_tau_preserves_heap safe_step_SucD
        safe_sucD(2) fst_conv)
     apply (meson order_refl safe_monoD safe_sucD(2) sup.cobounded2 sup_ge1; fail)
      (* subgoal: local frame opstep *)
    apply (clarsimp simp del: sup_apply)
    apply (rule conjI)
     apply (metis act.distinct(1) safe_sucE sup2I1 sup2I2)
    apply (simp only: disj.assoc[symmetric, of _ _ \<open>_ \<or> _\<close>])
    apply (erule disjE, erule disjE)
      apply (clarsimp simp add: conj_disj_distribR_middle[symmetric] conj_disj_distribL[symmetric])
      apply (meson inf_sup_ord(4) lessI order_le_less safe_mono sup.cobounded1; fail)
     apply (elim disjE; clarify)
      apply (frule(3) safe_sucD(3))
      apply (metis Suc.hyps opstep_tau_preserves_heap prod_eq_decompose(2) safe_step_SucD)
     apply (frule(3) safe_sucD(3))
     apply (metis Suc.hyps opstep_tau_preserves_heap prod_eq_decompose(2) safe_step_SucD)
    apply (elim disjE; clarify)
     apply (frule(3) safe_sucD(3))
     apply clarsimp
     apply (intro exI conjI, assumption, rule refl)
     apply (meson safe_mono order.refl sup_ge1; fail)
    apply (frule(3) safe_sucD(3))
    apply clarsimp
    apply (intro exI conjI, assumption, rule refl)
    apply (meson safe_mono order.refl sup_ge2; fail)
    done
qed blast

lemma safe_endet:
  \<open>safe R F Ga Ia qa n ca s \<Longrightarrow>
    safe R F Gb Ib qb n cb s \<Longrightarrow>
    Ia \<le> I \<Longrightarrow>
    Ib \<le> I \<Longrightarrow>
    Ga \<le> G \<Longrightarrow>
    Gb \<le> G \<Longrightarrow>
    qa \<le> q \<Longrightarrow>
    qb \<le> q \<Longrightarrow>
    safe R F G I q n (ca \<^bold>\<box> cb) s\<close>
  by (rule safe_monoD[OF safe_endet' order.refl order.refl _ _ _ order.refl])
    blast+



subsection \<open> Safety of parallel \<close>

lemma safe_parallel':
  \<open>safe (R \<squnion> Gb) (Ib \<squnion> Ib \<^emph>\<and> F) Ga Ia qa n ca (sla, ss) \<Longrightarrow>
    safe (R \<squnion> Ga) (Ia \<squnion> Ia \<^emph>\<and> F) Gb Ib qb n cb (slb, ss) \<Longrightarrow>
    sla ## slb \<Longrightarrow>
    safe R F (Ga \<squnion> Gb)
      (sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib)
      (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb)
      n (ca \<parallel> cb) (sla + slb, ss)\<close>
proof (induct n arbitrary: ca cb sla slb ss)
  case (Suc n)

  note safe_suc1 = safe_sucD[OF Suc.prems(1), simplified fst_conv snd_conv]
  note safe_suc2 = safe_sucD[OF Suc.prems(2), simplified fst_conv snd_conv]

  show ?case
  proof (rule safeI; fast?; (intro conjI)?; (simp only: fst_conv snd_conv)?)
    show \<open>(sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib) (sla + slb, ss)\<close>
      using Suc.prems(3) safe_suc1(2) safe_suc2(2)
      by (simp del: sup_apply,
          metis Suc.prems(1,2) safe_then_state_inv sepconj_conjI sswa_trivial)
  next
    fix m ss'
    assume r_step: \<open>R ss ss'\<close>
    presume m_eq_n: \<open>Suc m = Suc n\<close>

    show
      \<open>safe R F (Ga \<squnion> Gb)
        (sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib)
        (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb)
        m (ca \<parallel> cb) (sla + slb, ss')\<close>
      using r_step m_eq_n Suc.prems(1-3)
      apply (simp del: sup_apply)
      apply (intro Suc.hyps)
        apply fastforce
       apply (fastforce dest: safe_step_SucD[where c=ca and n=n])
      apply fast
      done
  next
    fix m \<alpha> s' c'
    assume step:
      \<open>opstep \<alpha> ((sla + slb, ss), ca \<parallel> cb) (s', c')\<close>
    presume m_eq_n:
      \<open>Suc m = Suc n\<close>

    have state_invs:
      \<open>Ia (sla, ss)\<close>
      \<open>Ib (slb, ss)\<close>
      using Suc.prems
      by blast+

    show \<open>\<alpha> \<noteq> Tau \<longrightarrow> (Ga \<squnion> Gb) ss (snd s')\<close>
      using step Suc.prems(3) state_invs
      apply clarsimp
      apply (elim disjE exE conjE)
       apply (force dest: safe_suc1(3))
      apply (simp add: partial_add_commute[of sla slb])
      apply (frule safe_suc2(3); blast dest: disjoint_sym)
      done
    show \<open>\<alpha> = Tau \<longrightarrow> fst s' = sla + slb\<close>
      using step
      by (metis fst_conv opstep_tau_preserves_heap)
    show \<open>safe R F (Ga \<squnion> Gb) (sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib) (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb) m
        c' s'\<close>
      using step state_invs m_eq_n Suc.prems(3)
      apply -
      apply clarsimp
      apply (elim disjE conjE exE)
        (* case: done *)
        apply (clarsimp simp del: sup_apply simp add: safe_skip_stable_iff
          sp_rely_sepconj_conj_semidistrib_mono)
        apply (metis Suc.prems(1-3) safe_then_postcond sepconj_conj_def sswa_trivial)
        (* case: left *)
       apply (frule safe_sucD(3)[OF Suc.prems(1), simplified fst_conv snd_conv])
         apply blast
        apply blast
       apply (clarsimp simp del: sup_apply)
       apply (rule Suc.hyps)
         apply blast
        apply (erule opstep_act_cases)
         apply (metis Suc.prems(2) fst_conv snd_conv safe_step_SucD)
        apply (blast intro: safe_suc2(1))
       apply blast
        (* case: right *)
      apply (simp add: partial_add_commute[of sla slb])
      apply (frule safe_suc2(3))
        apply (blast dest: disjoint_sym)
       apply blast
      apply (clarsimp simp del: sup_apply)
      apply (subst partial_add_commute, assumption)
      apply (rule Suc.hyps)
        apply (erule opstep_act_cases)
         apply (metis Suc.prems(1) safe_step_SucD fst_conv snd_conv)
        apply (blast intro: safe_suc1(1)[simplified fst_conv snd_conv])
       apply blast
      apply (blast dest: disjoint_sym)
      done
  next
    fix m \<alpha> c' sf slf' ss'
    assume assms2:
      \<open>sla + slb ## sf\<close>
      \<open>opstep \<alpha> ((sla + slb + sf, ss), ca \<parallel> cb) ((slf', ss'), c')\<close>
      \<open>F (sf, ss)\<close>

    presume m_eq_n:
      \<open>Suc m = Suc n\<close>

    have disjoint_parts:
      \<open>sla ## sf\<close>
      \<open>slb ## sf\<close>
      using Suc.prems(3) assms2(1)
      by (force dest: disjoint_add_leftL disjoint_add_leftR)+

    have framed_invs:
      \<open>(Ia \<squnion> Ia \<^emph>\<and> F) (sla + sf, ss)\<close>
      \<open>(Ib \<squnion> Ib \<^emph>\<and> F) (slb + sf, ss)\<close>
      using Suc.prems(1-2) assms2(1,3)
      by (metis disjoint_parts(1-2) safe_then_state_inv sepconj_conjI sup1CI)+

    show \<open>\<alpha> \<noteq> Tau \<longrightarrow> (Ga \<squnion> Gb) ss ss'\<close>
      using Suc.prems(3) assms2 disjoint_parts framed_invs safe_suc1(3) safe_suc2(3)
      by (clarsimp simp del: sup_apply,
          metis disjoint_add_swap_lr2 disjoint_sym_iff partial_add_assoc2 partial_add_commute)

    show \<open>\<exists>sl'.
            sl' ## sf \<and>
            slf' = sl' + sf \<and>
            (\<alpha> = Tau \<longrightarrow> sl' = sla + slb) \<and>
            safe R F (Ga \<squnion> Gb)
              (sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib)
              (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb)
              m c' (sl', ss')\<close>
      using assms2 m_eq_n Suc.prems(3) safe_suc1(1) safe_suc2(1) framed_invs
      apply (simp add: del: sup_apply)
      apply (elim disjE conjE exE)
        (* subgoal: done *)
        apply (clarsimp simp del: sup_apply simp add: safe_skip_stable_iff
          sp_rely_sepconj_conj_semidistrib_mono)
        apply (metis Suc.prems(1,2) safe_then_postcond safe_then_state_inv sepconj_conjI sswa_trivial)
        (* subgoal: left *)
       apply (simp add: partial_add_assoc2[of sla slb] del: sup_apply)
       apply (frule safe_suc1(3))
         apply (metis disjoint_add_swap_lr)
        apply blast
       apply (clarsimp simp del: sup_apply)
       apply (rule_tac x=\<open>sl' + slb\<close> in exI)
       apply (intro conjI)
          apply (metis disjoint_add_leftR disjoint_add_swap_rl)
         apply (metis disjoint_add_leftR partial_add_assoc3)
        apply blast
       apply (rule Suc.hyps)
         apply blast
        apply (erule opstep_act_cases)
         apply (cut_tac safe_step_SucD[OF Suc.prems(2)], force)
        apply blast
       apply (metis disjoint_add_rightL disjoint_parts(2))
        (* subgoal right *)
      apply (simp add: partial_add_commute[of sla] partial_add_assoc2[of slb]
          disjoint_sym_iff del: sup_apply)
      apply (frule safe_suc2(3))
        apply (metis disjoint_add_right_commute2 partial_add_commute)
       apply fast
      apply (clarsimp simp del: sup_apply)
      apply (rule_tac x=\<open>sla + sl'\<close> in exI)
      apply (intro conjI)
         apply (metis disjoint_parts(1) disjoint_add_right_commute2 disjoint_sym)
        apply (metis disjoint_parts(1) disjoint_add_rightL partial_add_assoc3 partial_add_commute)
       apply (blast dest: partial_add_commute)
      apply (rule Suc.hyps)
        apply (erule opstep_act_cases)
         apply (cut_tac safe_step_SucD[OF Suc.prems(1)], force)
        apply blast
       apply blast
      apply (metis disjoint_add_rightL disjoint_parts(1) disjoint_sym)
      done
  qed simp+
qed (blast intro: sepconj_conjI)

lemma safe_parallel:
  \<open>safe (R \<squnion> Gb) (Ib \<squnion> Ib \<^emph>\<and> F) Ga Ia qa n ca (sla, ss) \<Longrightarrow>
    safe (R \<squnion> Ga) (Ia \<squnion> Ia \<^emph>\<and> F) Gb Ib qb n cb (slb, ss) \<Longrightarrow>
    sla ## slb \<Longrightarrow>
    sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb \<le> q \<Longrightarrow>
    sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib \<le> I \<Longrightarrow>
    Ga \<squnion> Gb \<le> G \<Longrightarrow>
    safe R F G I q n (ca \<parallel> cb) (sla + slb, ss)\<close>
  using safe_parallel' safe_mono[OF order.refl order.refl _ _ _ order.refl]
  by meson


subsection \<open> Safety of conj \<close>

lemma safe_conj:
  assumes
    \<open>\<forall>lsa lsb fs ss.
      Ia (lsa, ss) \<longrightarrow> Ib (lsb, ss) \<longrightarrow> sswa (Ga \<sqinter> Gb) F (fs, ss) \<longrightarrow>
      lsa + fs = lsb + fs \<longrightarrow> lsa = lsb\<close>
  shows
    \<open>safe R F Ga Ia qa n c s \<Longrightarrow>
    safe R F Gb Ib qb n c s \<Longrightarrow>
    safe R F (Ga \<sqinter> Gb) (Ia \<sqinter> Ib) (qa \<sqinter> qb) n c s\<close>
proof (induct n arbitrary: c s)
  case (Suc n)
  show ?case
    using Suc.prems assms
    apply -
    apply (rule safeI)
        apply blast
       apply blast
      (* subgoal: rely *)
      apply (metis Suc.hyps Suc_inject safe_sucD(1))
      (* subgoal: opstep *)
     apply (clarsimp simp del: inf_apply)
     apply (frule safe_sucD(2)[where I=Ia and q=qa], blast)
     apply (frule safe_sucD(2)[where I=Ib and q=qb], blast)
     apply (clarsimp simp del: inf_apply)
     apply (rule conjI, blast)
     apply (metis Suc.hyps)
      (* subgoal: framed opstep *)
    apply (clarsimp simp del: inf_apply)
    apply (frule(3) safe_sucD(3)[where q=qa])
    apply (frule(3) safe_sucD(3)[where q=qb])
    apply (rule conjI, blast)
    apply (clarsimp simp del: inf_apply)
    apply (subgoal_tac \<open>(\<alpha> = Vis \<longrightarrow> Ga (snd s) ss' \<and> Gb (snd s) ss') \<and> (\<alpha> = Tau \<longrightarrow> ss' = snd s)\<close>)
     prefer 2
     apply (metis (no_types) opstep_tau_preserves_heap fst_conv snd_conv)
    apply (subgoal_tac \<open>sswa (Ga \<sqinter> Gb) F (fs, ss')\<close>)
     prefer 2
     apply (metis (full_types) act.exhaust inf2I sswa_step sswa_trivial)
    apply (metis Suc.hyps safe_then_state_inv)
    done
qed blast

lemma cancel_attempt1:
  fixes I F :: \<open>'r::perm_alg \<Rightarrow> bool\<close>
  defines \<open>lhs \<equiv> (\<forall>a b f. I a \<longrightarrow> I b \<longrightarrow> F f \<longrightarrow> a ## f \<longrightarrow> b ## f \<longrightarrow> a+f = b+f \<longrightarrow> a = b)\<close>
    and \<open>rhs \<equiv> (\<forall>ia\<le>I. \<forall>ib\<le>I. \<forall>f\<le>F. ia \<^emph> f \<noteq> \<bottom> \<longrightarrow> (ia \<^emph> f) = (ib \<^emph> f) \<longrightarrow> ia = ib)\<close>
  shows \<open>rhs \<Longrightarrow> lhs\<close>
    and \<open>R = {(a,b,a+b)|a b::'r. a ## b} \<Longrightarrow> lhs \<Longrightarrow> rhs\<close>
  unfolding lhs_def rhs_def
  apply -
    (* subgoal 1: rhs \<Rightarrow> lhs *)
   apply clarsimp
   apply (drule_tac x=\<open>(=) a\<close> in spec, drule mp, fast)
   apply (drule_tac x=\<open>(=) b\<close> in spec, drule mp, fast)
   apply (drule_tac x=\<open>(=) f\<close> in spec, drule mp, fast)
   apply (simp add: fun_eq_iff; fail)
    (* subgoal 2: lhs \<Rightarrow> rhs *)
  nitpick[card 'r=2]
  oops

lemma safe_Conj':
  assumes niassms:
    \<open>cancellative' (\<Squnion>\<I>) (\<Squnion>\<I>) (sswa (\<Squnion>\<G>) F)\<close>
    \<open>\<G> \<noteq> {}\<close>
    \<open>\<I> \<noteq> {}\<close>
    \<open>Q \<noteq> {}\<close>
    and iassms:
    \<open>\<forall>G\<in>\<G>. \<forall>I\<in>\<I>. \<forall>q\<in>Q. safe R F G I q n c s\<close>
  shows
    \<open>safe R F (\<Sqinter>\<G>) (\<Sqinter>\<I>) (\<Sqinter>Q) n c s\<close>
  using iassms
proof (induct n arbitrary: c s)
  case 0
  then show ?case
    using niassms(2-)
    by (force simp add: ball_conj_distrib)
next
  case (Suc n)
  show ?case
    using Suc.prems niassms
    apply -
    apply (rule safeI)
      (* termination *)
        apply (metis Suc.hyps Inf1_I safe_then_postcond)
      (* invariant *)
       apply (metis Suc.hyps Inf1_I safe_then_state_inv)
      (* rely step *)
      apply (clarsimp simp del: Inf_apply)
      apply (rule Suc.hyps; blast)
      (* opstep *)
     apply (clarsimp simp del: Inf_apply)
     apply (intro conjI)
       apply fastforce
      apply (metis fst_conv opstep_tau_preserves_heap)
     apply (metis Suc.hyps safe.cases)
      (* framed opstep *)
    apply (clarsimp simp del: inf_apply Inf_apply)
    apply (subgoal_tac \<open>(\<exists>G. G \<in> \<G>) \<and> (\<exists>I. I \<in> \<I>) \<and> (\<exists>q. q \<in> Q)\<close>)
     prefer 2
     apply blast
    apply (clarsimp simp del: inf_apply)
    apply (rename_tac Ga Ia qa)
    apply (frule bspec[of \<G>], assumption, drule bspec[of \<I>], assumption, drule bspec[of Q], assumption)
    apply (frule(3) safe_sucD(3))
    apply (clarsimp simp del: inf_apply)
    apply (rule conjI)
      (** guar *)
     apply (metis safe_sucE)
    apply (rule_tac x=sl' in exI)
    apply (intro conjI)
       apply blast
      apply blast
     apply blast
    apply (rule Suc.hyps)
    apply (clarsimp simp del: inf_apply)
    apply (rename_tac Gb Ib qb)
    apply (drule_tac x=Gb in bspec, assumption, drule_tac x=Ib in bspec, assumption,
        drule_tac x=qb in bspec, assumption)
    apply (frule(3) safe_sucD(3))
    apply (clarsimp simp del: inf_apply)
    apply (subgoal_tac \<open>sswa (\<Squnion>\<G>) F (fs, ss')\<close>)
     prefer 2
     apply (erule opstep_act_cases)
      apply force
     apply (clarsimp simp del: inf_apply)
     apply (rule sswa_step)
      apply (rule_tac r=Ga in Sup2_I)
       apply blast
      apply blast
     apply blast
    apply (simp add: cancellative'_def Bex_def imp_ex_conjL)
    apply (metis safe_then_state_inv)
    done
qed


section \<open> Soundness \<close>

lemma soundness:
  assumes \<open>rgsat c R G p q I F C\<close>
    and \<open>p s\<close>
    and \<open>C = \<top>\<close>
  shows \<open>safe R F G I q n c s\<close>
  using assms
proof (induct c R G p q I F C arbitrary: n s rule: rgsat.inducts)
  case (rgsat_skip R p q I C F G)
  then show ?case
    by (intro safe_skip[where p=p]; simp add: wlp_weaker_iff_sp_stronger)
next
  case (rgsat_iter c R G i I F C p q I')
  then show ?case
    apply (intro safe_iter[where i=\<open>sswa R i\<close> and R=R, simplified])
      apply (meson order.refl safe_monoD sswa_weaker; fail)
     apply blast
    apply blast
    done
next
  case (rgsat_seq ca r g p pp Ia F C cb q Ib I)
  then show ?case
    by (intro safe_seq) blast+
next
  case (rgsat_indet ca r ga p qa Ia F C cb gb qb Ib g q I)
  then show ?case
    by (intro safe_indet) blast+
next
  case (rgsat_endet c1 r Ga p qa Ia F C c2 Gb qb Ib g q I)
  then show ?case
    by (intro safe_endet) blast+
next
  case (rgsat_par ca R Gb Ga pa qa Ia Ib F C cb pb qb G p q I)
  moreover obtain sla slb ss where
    \<open>pa (sla, ss)\<close>
    \<open>pb (slb, ss)\<close>
    \<open>sla ## slb\<close>
    \<open>s = (sla + slb, ss)\<close>
    using rgsat_par.hyps(7) rgsat_par.prems(1)
    by (simp add: prod_eq_decompose le_fun_def sepconj_conj_apply, metis surjective_pairing)
  ultimately show ?case
    by (simp del: sup_apply top_apply,
        intro safe_parallel[where Ga=Ga and Gb=Gb and Ia=Ia and Ib=Ib and qa=qa and qb=qb];
        simp del: sup_apply top_apply)
next
  case (rgsat_atom p' R p q q' ar G F I C)
  then show ?case
    apply (intro safe_atom[where p=\<open>wssa R p\<close> and q=q])
           apply (simp del: top_apply, metis order.trans wlp_weaker_iff_sp_stronger wssa_stronger)
          apply (simp del: top_apply, meson order_trans sepconj_conj_monoL sp_pred_mono
        wssa_stronger; fail)
        apply (simp del: top_apply)
        apply (rule order.trans[OF rel_image_mono, rotated], assumption)
        apply (simp add: rel_image_mono inf_commute le_infI2 sepconj_conj_monoL sup.coboundedI1
        sup.coboundedI2 wssa_stronger; fail)
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
    done
next
  case (rgsat_frame c R G p q I F F' C)
  then show ?case
    apply -
    apply (clarsimp simp add: sepconj_conj_apply[where s=s] simp del: top_apply sup_apply)
    apply (rename_tac ls fs)
    apply (rule_tac s=\<open>(ls, snd s)\<close> in safe_frame)
        apply force
       apply force
      apply (simp add: split_pairs2; fail)
     apply assumption
    apply force
    done
next
  case (rgsat_weaken c R' G' p' q' I' F' C p q R G I F)
  moreover have \<open>p' s\<close>
    using rgsat_weaken.hyps(3) rgsat_weaken.prems
    by blast
  moreover then have \<open>safe R' F' G' I' q' n c s\<close>
    using rgsat_weaken.prems rgsat_weaken.hyps(2)
    by fast
  ultimately show ?case
    by (meson order.refl safe_monoD)
next
  case rgsat_Disj
  then show ?case by fast
next
  case (rgsat_Conj \<I> I' \<G> G' Q q' c R p F C)
  have Aa: \<open>\<forall>n. \<forall>G\<in>\<G>. \<forall>I\<in>\<I>. \<forall>q\<in>Q. safe R F G I q n c s\<close>
    using rgsat_Conj.hyps(7) rgsat_Conj.prems(1,2)
    by blast
  then show ?case
    using rgsat_Conj.prems safe_Conj'[OF rgsat_Conj(8) rgsat_Conj(5,4,6)]
      rgsat_Conj.hyps(1-3)
    by (meson safe_mono_guarD safe_mono_invD safe_mono_postD)
qed

end