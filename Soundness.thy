theory Soundness
  imports RGLogic
begin

section \<open> Operational Semantics \<close>

type_synonym 's pconfig = \<open>'s \<times> 's comm\<close>

subsection \<open> Actions \<close>

datatype 'a act = Tau | Vis 'a

lemma act_not_eq_iff[simp]:
  \<open>\<alpha> \<noteq> Tau \<longleftrightarrow> (\<exists>x. \<alpha> = Vis x)\<close>
  \<open>(\<forall>x. \<alpha> \<noteq> Vis x) \<longleftrightarrow> \<alpha> = Tau\<close>
  by (meson act.distinct act.exhaust)+

lemma ex_act_neq[simp]:
  \<open>\<exists>\<alpha>. \<alpha> \<noteq> Vis x\<close>
  \<open>\<exists>\<alpha>. \<alpha> \<noteq> Tau\<close>
  by blast+


subsection \<open> Operational semantics steps \<close>

fun opstep :: \<open>unit act \<Rightarrow> 's pconfig \<Rightarrow> 's pconfig \<Rightarrow> bool\<close> where
  \<open>opstep \<alpha> (s, Done r) sc' \<longleftrightarrow> False\<close>
| \<open>opstep \<alpha> (s, ca ;; cb) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    \<alpha> = Tau \<and> ca = Crash \<and> sc' = (s, Crash) \<or>
    (\<exists>s' ca'. opstep \<alpha> (s, ca) (s', ca') \<and> sc' = (s', ca' ;; cb))\<close>
| \<open>opstep \<alpha> (s, ca \<^bold>\<sqinter> cb) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> sc' = (s, ca) \<or>
    \<alpha> = Tau \<and> sc' = (s, cb)\<close>
| \<open>opstep \<alpha> (s, ca \<^bold>\<box> cb) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> ca = Crash \<and> sc' = (s, Crash) \<or>
    \<alpha> = Tau \<and> cb = Crash \<and> sc' = (s, Crash) \<or>
    \<alpha> = Tau \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    \<alpha> = Tau \<and> cb = Skip \<and> sc' = (s, ca) \<or>
    \<alpha> = Tau \<and> (\<exists>s' ca'. sc' = (s', ca' \<^bold>\<box> cb) \<and> opstep Tau (s, ca) (s', ca')) \<or>
    \<alpha> = Tau \<and> (\<exists>s' cb'. sc' = (s', ca \<^bold>\<box> cb') \<and> opstep Tau (s, cb) (s', cb')) \<or>
    \<alpha> \<noteq> Tau \<and> opstep \<alpha> (s, ca) sc' \<or>
    \<alpha> \<noteq> Tau \<and> opstep \<alpha> (s, cb) sc'\<close>
| \<open>opstep \<alpha> (s, ca \<parallel> cb) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> ca = Crash \<and> sc' = (s, Crash) \<or>
    \<alpha> = Tau \<and> cb = Crash \<and> sc' = (s, Crash) \<or>
    \<alpha> = Tau \<and> ca = Skip \<and> cb = Skip \<and> sc' = (s, Skip) \<or>
    (\<exists>s' ca'. opstep \<alpha> (s, ca) (s', ca') \<and> sc' = (s', ca' \<parallel> cb)) \<or>
    (\<exists>s' cb'. opstep \<alpha> (s, cb) (s', cb') \<and> sc' = (s', ca \<parallel> cb'))\<close>
| \<open>opstep \<alpha> (s, DO c OD) sc' \<longleftrightarrow>
    \<alpha> = Tau \<and> c = Crash \<and> sc' = (s, Crash) \<or>
    \<alpha> = Tau \<and> c \<noteq> Crash \<and> (\<forall>\<alpha>' sc'. \<not> opstep \<alpha>' (s, c) sc') \<and> sc' = (s, Skip) \<or>
    (\<exists>s' c'. opstep \<alpha> (s, c) (s', c') \<and> sc' = (s', c' ;; DO c OD))\<close>
| \<open>opstep \<alpha> (s, Atomic ap aq) sc' \<longleftrightarrow>
    (\<exists>a. \<alpha> = Vis a \<and>
      (ap s \<and> aq s (fst sc') \<and> snd sc' = Skip \<or>
        \<not> ap s \<and> fst sc' = s \<and> snd sc' = Crash))\<close>


paragraph \<open> Pretty operational semantics \<close>

abbreviation pretty_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>sc \<midarrow>\<alpha>\<rightarrow> msc' \<equiv> opstep \<alpha> sc msc'\<close>

abbreviation pretty_no_opstep :: \<open>_ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>'/\<rightarrow>\<close> [60] 60) where
  \<open>sc \<midarrow>/\<rightarrow> \<equiv> \<forall>\<alpha> sc'. opstep \<alpha> sc sc'\<close>


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
    \<open>(s, c) \<midarrow>Vis x\<rightarrow> (s', c')\<close>
  shows
    \<open>\<exists>p q. (p, q) \<in># head_atoms c \<and> (p s \<longrightarrow> q s s')\<close>
proof -
  { fix \<alpha> sc sc'
    have
      \<open>sc \<midarrow>\<alpha>\<rightarrow> sc' \<Longrightarrow>
        sc = (s, c) \<Longrightarrow>
        sc' = (s', c') \<Longrightarrow>
        \<alpha> = Vis x \<Longrightarrow>
        \<exists>p q. (p, q) \<in># head_atoms c \<and> (p s \<longrightarrow> q s s')\<close>
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
    (\<And>x. \<alpha> = Vis x \<Longrightarrow> s \<midarrow>Vis x\<rightarrow> s' \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  by (metis act.exhaust opstep_tau_preserves_heap)

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
    \<alpha> = Vis () \<and> 
    fst sc' = s \<and>
    (p s \<and> snd sc' = Skip \<or>
      \<not> p s \<and> snd sc' = Crash)\<close>
  by (force simp add: Assert_def)

paragraph \<open> Await \<close>

lemma opstep_await_iff[simp]:
  \<open>opstep \<alpha> (s, Await p) sc' \<longleftrightarrow>
    \<alpha> = Vis () \<and>
    p s \<and>
    sc' = (s, Skip)\<close>
  by (cases sc', force simp add: Await_def)

paragraph \<open> IfThenElse \<close>

lemma opstep_IfThenElse_iff[simp]:
  \<open>opstep \<alpha> (s, IfThenElse p ct cf) sc' \<longleftrightarrow>
    \<alpha> = Vis () \<and> (
      p s \<and> sc' = (s, Skip ;; ct) \<or>
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
  state invariant \<open>I\<close> and all local steps must fulfil the guarantee condition \<open>G\<close>. In addition,
  the execution must always finish by terminating (not crashing), and uphold the postcondition \<open>q\<close>.
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
  where
  safe_nil[intro!]: \<open>safe R F G I q 0 c s\<close>
| safe_suc[intro]:
  \<open>\<comment> \<open> If the command is Done, we are terminated and the postcondition is established.
        Note: this means that a terminated branch of the tree has infinite final stuttering. \<close>
    (\<forall>r. c = Done r \<longrightarrow> r = Term \<and> q s) \<Longrightarrow>
    \<comment> \<open> the current state obeys the state invariant \<close>
    I s \<Longrightarrow>
    \<comment> \<open> rely steps are safe \<close>
    (\<And>ss'. R (snd s) ss' \<Longrightarrow> safe R F G I q n c (fst s, ss')) \<Longrightarrow>
    \<comment> \<open> closed under framed opsteps \<close>
    (\<And>f \<alpha> slf' ss' c'.
        fst s ## f \<Longrightarrow>
        ((fst s + f, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((slf', ss'), c') \<Longrightarrow>
        F (f, snd s) \<Longrightarrow>
        \<comment> \<open> Non-tau steps establish the guarantee. \<close>
        (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) ss') \<and>
        \<comment> \<open> Note the existential! We only guarantee \<^emph>\<open>one\<close> such unframed state is safe.
             This is only relevant for non-cancellative frame, in which case the states in question
              are a verification fiction anyway, so this is reasonable. \<close>
        (\<exists>sl'.
          sl' ## f \<and>
          slf' = sl' + f \<and>
          (\<alpha> = Tau \<longrightarrow> sl' = fst s) \<and> \<comment> \<open> Tau moves are not allowed to change the fictive state! \<close>
          safe R F G I q n c' (sl', ss'))) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe R F G I q (Suc n) c s\<close>


subsection \<open> Proofs about safe \<close>

inductive_cases safe_zeroE[elim!]: \<open>safe R F G I q 0 c s\<close>
inductive_cases safe_sucE[elim]: \<open>safe R F G I q (Suc n) c s\<close>

lemma safe_then_state:
  assumes \<open>safe R F G I q (Suc n) c s\<close>
  shows \<open>I s\<close>
proof -
  { fix m s
    have \<open>safe R F G I q m c s \<Longrightarrow> 0 < (m::nat) \<Longrightarrow> I s\<close>
      by (induct rule: safe.inducts) blast+
  } then show ?thesis
    using assms by blast
qed

lemma safe_nil_iff[simp]:
  \<open>safe R F G I q 0 c s\<close>
  by force

lemma safe_suc_iff:
  \<open>safe R F G I q (Suc n) c s \<longleftrightarrow>
    (\<forall>r. c = Done r \<longrightarrow> r = Term \<and> q s) \<and>
    I s \<and>
    (\<forall>ss'. R (snd s) ss' \<longrightarrow> safe R F G I q n c (fst s, ss')) \<and>
    (\<forall>f \<alpha> slf' ss' c'.
        fst s ## f \<longrightarrow>
        ((fst s + f, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((slf', ss'), c') \<longrightarrow>
        F (f, snd s) \<longrightarrow>
        (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) ss') \<and>
        (\<exists>sl'.
          sl' ## f \<and>
          slf' = sl' + f \<and>
          (\<alpha> = Tau \<longrightarrow> sl' = fst s) \<and>
          safe R F G I q n c' (sl', ss')))\<close>
  apply (rule iffI)
   apply (elim safe_sucE; simp; fail)
  apply (cases s, simp, rule safe_suc; force)
  done

lemma safe_sucD:
  \<open>safe R F G I q (Suc n) c s \<Longrightarrow> c = Done r \<Longrightarrow> r = Term\<close>
  \<open>safe R F G I q (Suc n) c s \<Longrightarrow> c = Done r \<Longrightarrow> q s\<close>
  \<open>safe R F G I q (Suc n) c s \<Longrightarrow> I s\<close>
  \<open>safe R F G I q (Suc n) c s \<Longrightarrow> R ss ss' \<Longrightarrow> ss = snd s \<Longrightarrow> safe R F G I q n c (fst s, ss')\<close>
  \<open>safe R F G I q (Suc n) c s \<Longrightarrow>
    sl ## f \<Longrightarrow>
    ((sl + f, ss), c) \<midarrow>\<alpha>\<rightarrow> ((slf', ss'), c') \<Longrightarrow>
    F (f, ss) \<Longrightarrow>
    s = (sl, ss) \<Longrightarrow>
    (\<alpha> \<noteq> Tau \<longrightarrow> G ss ss') \<and>
    (\<exists>sl'.
      sl' ## f \<and>
      slf' = sl' + f \<and>
      (\<alpha> = Tau \<longrightarrow> sl' = sl) \<and>
      safe R F G I q n c' (sl', ss'))\<close>
  by (erule safe_sucE, force)+


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
   apply blast
  apply (case_tac m, force)
  apply clarsimp
  apply (rename_tac m)
  apply (rule safe_suc)
     apply fastforce
    apply (metis predicate1D)
   apply (simp, metis predicate2D)
  apply simp
  apply (drule meta_spec, drule meta_spec2, drule meta_spec2, drule meta_mp, assumption,
      drule meta_mp, assumption)
  apply blast
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


lemma safe_step_SucD:
  \<open>safe R F G I q (Suc n) c s \<Longrightarrow> safe R F G I q n c s\<close>
  by (metis safe_mono_stepsD le_add2 plus_1_eq_Suc)


subsection \<open> Safety of Skip \<close>

lemma safe_term_iff:
  \<open>safe R F G I q n (Skip) s \<longleftrightarrow>
    (\<exists>sl ss. s = (sl, ss) \<and> (\<forall>k<n. \<forall>ss'. (R^^k) ss ss' \<longrightarrow> q (sl, ss') \<and> I (sl, ss')))\<close>
  apply (induct n arbitrary: s)
   apply (simp; fail)
  apply (rule iffI)
   apply (erule safe_sucE)
   apply (clarsimp simp add: less_Suc_eq_0_disj)
   apply (metis relpowp_Suc_D2')
  apply (simp add: safe_suc_iff)
  apply (metis Suc_mono prod_eq_decompose(2) relpowp_0_I relpowp_Suc_I2 zero_less_Suc)
  done

lemma safe_term_stable_iff:
  assumes
    \<open>sswa R I \<le> I\<close>
    \<open>sswa R q \<le> q\<close>
  shows
    \<open>safe R F G I q n (Skip) s \<longleftrightarrow>
      (\<exists>hl hs. s = (hl, hs) \<and> (0 < n \<longrightarrow> q (hl, hs) \<and> I (hl, hs)))\<close>
proof -
  have \<open>\<And>n' hl hs.
          (\<forall>k\<le>n'. \<forall>hs'. (R ^^ k) hs hs' \<longrightarrow> q (hl, hs') \<and> I (hl, hs')) \<longleftrightarrow>
            q (hl, hs) \<and> I (hl, hs)\<close>
    using assms
    apply (simp add: le_fun_def sp_def imp_ex_conjL rtranclp_power)
    apply (metis le0 relpowp_0_I)
    done
  then show ?thesis
    apply (cases n, force)
    apply (rule trans[OF safe_term_iff])
    apply (clarsimp simp add: less_Suc_eq_le)
    done
qed

lemma safe_term':
  \<open>wssa R q s \<Longrightarrow> wssa R I s \<Longrightarrow> safe R F G I q n (Skip) s\<close>
  apply (induct n arbitrary: s)
   apply force
  apply (case_tac s)
  apply clarsimp
  apply (rule safe_suc)
     apply force
    apply force
   apply (simp add: wssa_step; fail)
  apply force
  done

lemma safe_term:
  \<open>p s \<Longrightarrow> p \<le> wssa R q \<Longrightarrow> p \<le> wssa R I \<Longrightarrow> safe R F G I q n (Skip) s\<close>
  apply (rule safe_monoD[OF _ order.refl order.refl order.refl order.refl order.refl order.refl])
  apply (rule safe_term'[where q=\<open>q\<close>])
   apply blast
  apply blast
  done

lemma safe_crash_iff[simp]:
  \<open>safe R F G I q n (Crash) s \<longleftrightarrow> n = 0\<close>
  by (induct n) force+


subsection \<open> Safety of frame \<close>

lemma safe_frame':
  \<open>safe R F G I q n c s \<Longrightarrow>
    s = (sl, ss) \<Longrightarrow>
    sl ## sf \<Longrightarrow>
    sswa (R \<squnion> G) F' (sf, ss) \<Longrightarrow>
    safe R (sswa (R \<squnion> G) F' \<midarrow>\<^emph>\<^sub>\<and> F) G (I \<^emph>\<and> sswa (R \<squnion> G) F') (q \<^emph>\<and> sswa (R \<squnion> G) F') n c (sl + sf, ss)\<close>
proof (induct arbitrary: sl ss sf rule: safe.induct)
  case (safe_nil c s)
  then show ?case by (metis safe.safe_nil)
next
  case (safe_suc c s n)

  note hyps = safe_suc.hyps[simplified safe_suc.prems(1)[simplified]]

  show ?case
    using safe_suc.prems(2-)
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
       apply (clarsimp simp add: sepconj_conj_def simp del: sup_apply)
       apply (metis hyps(1))
      (* subgoal: stateset *)
      apply (meson hyps(2) predicate1D sepconj_conjI; fail)
      (* subgoal: rely step *)
     apply (simp del: sup_apply)
     apply (rule hyps(4), force, force, force)
     apply (rule sswa_step, rule sup2I1, blast, blast)
      (* subgoal: local framed opstep *)
    apply (clarsimp simp add: partial_add_assoc2[of sl sf] simp del: sup_apply)
    apply (frule hyps(5)[simplified fst_conv snd_conv, rotated 1])
      apply (clarsimp simp add: sepimp_conj_apply simp del: sup_apply)
      apply (metis disjoint_add_leftR disjoint_sym_iff partial_add_commute)
     apply (metis disjoint_add_swap_lr)
    apply (clarsimp simp del: sup_apply)
    apply (rule_tac x=\<open>sl' + sf\<close> in exI, rule conjI)
     apply (metis disjoint_add_leftR disjoint_add_swap_rl)
    apply (rule conjI)
     apply (metis disjoint_add_leftR partial_add_assoc3)
    apply (clarsimp simp del: sup_apply)
    apply (erule opstep_act_cases)
     apply force
    apply (frule sswa_stepD, force)
    apply (metis disjoint_add_leftR disjoint_add_rightL)
    done
qed

lemma safe_frame:
  \<open>safe R Fa G I q n c (sl, ss) \<Longrightarrow>
    Fb (sf, ss) \<Longrightarrow>
    sl ## sf \<Longrightarrow>
    s' = (sl + sf, ss) \<Longrightarrow>
    I \<^emph>\<and> sswa (R \<squnion> G) Fb \<le> I' \<Longrightarrow>
    F' \<le> sswa (R \<squnion> G) Fb \<midarrow>\<^emph>\<^sub>\<and> Fa \<Longrightarrow>
    q \<^emph>\<and> sswa (R \<squnion> G) Fb \<le> q' \<Longrightarrow>
    safe R F' G I' q' n c s'\<close>
  apply (rule safe_monoD[OF _ order.refl _ order.refl _ _ order.refl, rotated])
     apply assumption
    apply assumption
   apply assumption
  apply clarsimp
  apply (rule safe_frame'; blast)
  done


subsection \<open> Safety of Atomic \<close>

(* TODO: move *)
definition
  \<open>rel_restr_fst r \<equiv> \<lambda>y y'. \<exists>x x'. r (x,y) (x',y')\<close>

lemma rel_restr_fst_of_top_relTimes_eq[simp]:
  \<open>rel_restr_fst (\<top> \<times>\<^sub>R r) = r\<close>
  by (simp add: rel_restr_fst_def rel_Times_def fun_eq_iff)

lemma rel_restr_fst_conj_semidistrib:
  \<open>rel_restr_fst (ra \<sqinter> rb) \<le> rel_restr_fst ra \<sqinter> rel_restr_fst rb\<close>
  by (force simp add: rel_restr_fst_def le_fun_def)

lemma rel_restr_fst_galois:
  \<open>rel_restr_fst r \<le> r' \<longleftrightarrow> r \<le> \<top> \<times>\<^sub>R r'\<close>
  by (force simp add: rel_restr_fst_def le_fun_def)


lemma safe_atom':
  \<open>wssa R p \<^emph>\<and> F \<le> ap \<Longrightarrow>
    \<forall>f\<le>F. sp aq (wssa R p \<^emph>\<and> f) \<le> q \<^emph>\<and> f \<Longrightarrow>
    wssa R p s \<Longrightarrow>
    safe R F
      (rel_restr_fst (rel_liftL (wssa R p \<^emph>\<and> F) \<sqinter> aq)) \<comment> \<open> G \<close>
      (wssa R p \<squnion> sswa R q) \<comment> \<open> I \<close>
      (sswa R q) \<comment> \<open> q \<close>
      n (Atomic ap aq) s\<close>
proof (induct n arbitrary: s)
  case 0 then show ?case by force
next
  case (Suc n)
  show ?case
    using Suc.prems
    apply -
    apply (cases s)
    apply (rename_tac sl ss)
    apply (clarsimp simp del: sup_apply inf_apply top_apply rel_liftL_apply rel_lift_apply)
    apply (rule safe_suc)
      (* subgoal: termination *)
       apply force
      (* subgoal: stateset *)
      apply force
      (* subgoal: rely *)
     apply (simp only: fst_conv snd_conv)
     apply (rule Suc.hyps[simplified fst_conv snd_conv])
       apply blast
      apply blast
     apply (meson wssa_step; fail)
      (* subgoal: local framed opstep *)
    apply (rule conjI)
      (* subsubgoal: guarantee *)
     apply (clarsimp simp add: rel_restr_fst_def)
     apply (meson predicate1D sepconj_conjI; fail)
      (* subsubgoal: safety after opstep *)
    apply (subgoal_tac \<open>ap (sl + f, ss)\<close>)
     prefer 2
     apply (simp only: fst_conv snd_conv)
     apply (meson predicate1D sepconj_conjI; fail)
    apply (subgoal_tac \<open>sswa R (wssa R p \<squnion> sswa R q) \<le> wssa R p \<squnion> sswa R q\<close>)
     prefer 2
     apply (simp add: sp_sup; fail)
    apply (clarsimp simp del: sup_apply inf_apply top_apply rel_liftL_apply rel_lift_apply
        simp add: safe_term_stable_iff)
    apply (clarsimp simp add: sp_def[of aq] le_fun_def imp_ex_conjL)
    apply (drule_tac x=\<open>(=) (f, ss)\<close> in spec)
    apply clarsimp
    apply (drule spec2, drule spec2, drule mp, assumption)
    apply (drule mp, force simp add: sepconj_conjI)
    apply (fastforce simp add: sepconj_conj_def)
    done
qed

lemma safe_atom:
  \<open>wssa R p \<^emph>\<and> F \<le> ap \<Longrightarrow>
    \<forall>f\<le>F. sp aq (wssa R p \<^emph>\<and> f) \<le> q \<^emph>\<and> f \<Longrightarrow>
    rel_restr_fst (rel_liftL (wssa R p \<^emph>\<and> F) \<sqinter> aq) \<le> G \<Longrightarrow>
    wssa R p s \<Longrightarrow>
    sswa R q \<le> q' \<Longrightarrow>
    wssa R p \<le> I \<Longrightarrow>
    sswa R q \<le> I \<Longrightarrow>
    safe R F G I q' n (Atomic ap aq) s\<close>
  apply (rule safe_monoD[OF _ order.refl order.refl _ _ _ order.refl, rotated])
     apply assumption
    apply (rule sup_least[of \<open>wssa R p\<close> _ \<open>sswa R q\<close>]; assumption)
   apply assumption
  apply (rule safe_atom'; fast)
  done


subsection \<open> Safety of Sequencing \<close>

lemma safe_seq_assoc_left:
  \<open>safe R F G I q n c s \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe R F G I q n ((c1 ;; c2) ;; c3) s\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
     apply blast
    apply blast
   apply blast
  apply clarsimp
  apply (elim disjE)
    apply force
   apply force
  apply metis
  done

\<comment> \<open> Not true because crash under a left-seq takes an extra step. \<close>
lemma safe_seq_assoc_right:
  \<open>safe R F G I q n c s \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    safe R F G I q n (c1 ;; c2 ;; c3) s\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
     apply blast
    apply blast
   apply blast
  apply clarsimp
  apply (elim disjE)
    apply force
   apply clarsimp
  oops

lemma safe_seq':
  \<open>safe R F G Ia q n ca s \<Longrightarrow>
    (\<forall>m\<le>n. \<forall>s'. q s' \<longrightarrow> safe R F G Ib q' m cb s') \<Longrightarrow>
    safe R F G (Ia \<squnion> Ib) q' n (ca ;; cb) s\<close>
proof (induct arbitrary: cb q' rule: safe.inducts)
  case (safe_suc c s n)

  have safe_c2:
    \<open>\<And>m s'. m \<le> n \<Longrightarrow> q s' \<Longrightarrow> safe R F G Ib q' m cb s'\<close>
    \<open>\<And>s'. q s' \<Longrightarrow> safe R F G Ib q' (Suc n) cb s'\<close>
    by (simp add: safe_suc.prems[simplified fst_conv snd_conv])+
  then show ?case
    using safe_suc.prems(1) safe_suc.hyps(1)
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
        apply force
      (* subgoal: stateset *)
       apply (simp add: safe_suc.hyps(2); fail)
      (* subgoal: rely *)
      apply (metis safe_suc.hyps(4))
      (* subgoal: local framed opstep *)
    apply (clarsimp simp del: sup_apply)
    apply (elim disjE conjE exE)
      (** term *)
      apply clarsimp
      apply (meson order.refl inf_sup_ord(4) safe_c2(1) safe_monoD; fail)
      (** crash *)
     apply blast
      (** step *)
    apply (frule(2) safe_suc.hyps(5))
    apply (metis act.distinct(1) safe_c2(1))
    done
qed force

lemma safe_seq:
  \<open>safe R F G Ia q n ca s \<Longrightarrow>
    (\<forall>s'. q s' \<longrightarrow> safe R F G Ib q' n cb s') \<Longrightarrow>
    Ia \<le> I \<Longrightarrow>
    Ib \<le> I \<Longrightarrow>
    safe R F G I q' n (ca ;; cb) s\<close>
  apply (rule safe_monoD[where I=\<open>Ia \<squnion> Ib\<close>,
        OF _ order.refl order.refl order.refl _ order.refl order.refl])
   apply (rule safe_seq', blast)
   apply (meson order.refl safe_monoD; fail)
  apply force
  done


subsection \<open> Safety of Iter \<close>

lemma safe_iter':
  \<open>\<forall>s'. wssa R i s' \<longrightarrow> safe R F G I (wssa R i) n c s' \<Longrightarrow>
    wssa R i s \<Longrightarrow>
    safe R F G I (wssa R i) n (Iter c) s\<close>
proof (induct n arbitrary: i s)
  case (Suc n)

  have safe_ih:
    \<comment> \<open> we never need to go back beyond \<open>n\<close> \<close>
    \<open>\<And>s'. wssa R i s' \<Longrightarrow> safe R F G I (wssa R i) n c s'\<close>
    \<open>\<And>s'. wssa R i s' \<Longrightarrow> safe R F G I (wssa R i) (Suc n) c s'\<close>
    using Suc.prems(1) safe_mono_steps[OF le_SucI[OF order.refl]]
    by blast+

  note safe_suc_c = safe_sucD[OF safe_ih(2)]

  show ?case
    using Suc.prems(2)
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
       apply blast
      (* subgoal: stateset *)
      apply (metis safe_suc_c(3))
      (* subgoal: rely *)
     apply (rule Suc.hyps[where i=i])
      apply (simp add: safe_ih(1); fail)
     apply (simp add: wssa_step; fail)
      (* subgoal: locally framed opstep *)
    apply (subgoal_tac \<open>c \<noteq> Crash\<close>)
     prefer 2
     apply (metis safe_suc_c(1) tres.simps(2))
    apply (simp add: le_fun_def del: split_paired_All)
    apply (rule conjI)
      (** guar *)
     apply (metis safe_suc_c(5) act.distinct(1) prod.collapse)
      (** step *)
    apply (elim disjE conjE exE)
      (*** loop-end *)
     apply simp
     apply (rule safe_term')
      apply force
     apply (force intro: safe_suc_c(3) predicate1D[OF wssa_stronger_strengthen[where p=i]])
      (*** step *)
    apply (clarsimp simp add: safe_suc_iff simp del: split_paired_All)
    apply (rename_tac c')
    apply (frule(3) safe_suc_c(5), force)
    apply clarsimp
    apply (intro exI conjI)
       prefer 4
       apply (rule safe_seq[where q=\<open>wssa R i\<close>, OF _ _ order.refl order.refl])
        apply blast
       apply (intro allI impI)
       apply (rule safe_mono_post[where q=\<open>wssa R i\<close>])
        apply force
       apply (rule Suc.hyps)
        apply (blast intro: safe_ih(1))
       apply blast
      apply blast
     apply blast
    apply blast
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
    \<open>safe R F G I q n ca s \<Longrightarrow>
      safe R F G I q n cb s \<Longrightarrow>
      safe R F G I q n (ca \<^bold>\<sqinter> cb) s\<close>
proof (induct n arbitrary: ca cb s)
  case (Suc n)

  show ?case
    using Suc.prems
    apply -
    apply (rule safe_suc)
      (* subgoal: rely *)
       apply blast
      (* subgoal: stableset *)
      apply blast
      (* subgoal: rely *)
     apply (rule Suc.hyps)
      apply (blast dest: safe_sucD)
     apply (blast dest: safe_sucD)
      (* subgoal: framed opstep *)
    apply (clarsimp simp add: conj_disj_distribL[symmetric] simp del: sup_apply)
    apply (metis safe_step_SucD)
    done
qed blast

lemma safe_indet:
  \<open>safe R F G Ia q n ca s \<Longrightarrow>
      safe R F G Ib q n cb s \<Longrightarrow>
      Ia \<squnion> Ib \<le> I \<Longrightarrow>
      safe R F G I q n (ca \<^bold>\<sqinter> cb) s\<close>
  using safe_indet'
  by (metis safe_mono_invD sup.cobounded1 sup.cobounded2)


subsubsection \<open> Safety of external nondeterminism \<close>

lemma safe_endet':
  \<open>safe R F G I q n ca s \<Longrightarrow>
    safe R F G I q n cb s \<Longrightarrow>
    safe R F G I q n (ca \<^bold>\<box> cb) s\<close>
proof (induct n arbitrary: ca cb s)
  case (Suc n)
  show ?case
    using Suc.prems
    apply -
    apply (rule safe_suc)
      (* subgoal: skip *)
       apply blast
      (* subgoal: stableset *)
      apply blast
      (* subgoal: rely *)
     apply (rule Suc.hyps)
      apply (blast dest: safe_sucD)
     apply (blast dest: safe_sucD)
      (* subgoal: local frame opstep *)
    apply clarsimp
    apply (elim disjE conjE exE)
           apply blast
          apply blast
         apply (metis act.distinct(1) safe_step_SucD surjective_pairing)
        apply (metis act.distinct(1) safe_step_SucD surjective_pairing)
       apply (frule opstep_tau_preserves_heap)
       apply (clarsimp del: safe_sucE elim!: safe_sucE)
       apply (rule Suc.hyps[OF _ safe_step_SucD[OF Suc.prems(2)]])
       apply (metis surjective_pairing)
      apply (frule opstep_tau_preserves_heap)
      apply (clarsimp del: safe_sucE elim!: safe_sucE)
      apply (rule Suc.hyps[OF safe_step_SucD[OF Suc.prems(1)]])
      apply (metis surjective_pairing)
     apply blast
    apply blast
    done
qed blast

lemma safe_endet:
  \<open>safe R F G Ia q n ca s \<Longrightarrow>
    safe R F G Ib q n cb s \<Longrightarrow>
    Ia \<squnion> Ib \<le> I \<Longrightarrow>
    safe R F G I q n (ca \<^bold>\<box> cb) s\<close>
  using safe_endet'
  by (metis le_supE safe_mono_inv)


subsection \<open> Safety of parallel \<close>

lemma safe_parallel':
  \<open>safe (R \<squnion> Gb) (Ib \<^emph>\<and> F) Ga Ia (sswa (R \<squnion> Gb) qa) n ca (sla, ss) \<Longrightarrow>
    safe (R \<squnion> Ga) (Ia \<^emph>\<and> F) Gb Ib (sswa (R \<squnion> Ga) qb) n cb (slb, ss) \<Longrightarrow>
    sla ## slb \<Longrightarrow>
    safe R F (Ga \<squnion> Gb)
      (sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib)
      (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb)
      n (ca \<parallel> cb) (sla + slb, ss)\<close>
proof (induct n arbitrary: ca cb sla slb ss)
  case (Suc n)

  note safe_suc1 = safe_sucD[OF Suc.prems(1)]
  note safe_suc2 = safe_sucD[OF Suc.prems(2)]

  show ?case
  proof (rule safe_suc; fast?; (intro conjI)?; (simp only: fst_conv snd_conv)?)
    show \<open>(sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib) (sla + slb, ss)\<close>
      using Suc.prems(3) safe_suc1(3) safe_suc2(3)
      by (meson sepconj_conjI sswa_trivial)
  next
    fix ss'
    assume \<open>R ss ss'\<close>
    then show
      \<open>safe R F (Ga \<squnion> Gb)
        (sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib)
        (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb)
        n (ca \<parallel> cb) (sla + slb, ss')\<close>
      using Suc.prems(1-3)
      by (intro Suc.hyps; force)
  next
    fix \<alpha> c' sf slf' ss'
    assume assms2:
      \<open>sla + slb ## sf\<close>
      \<open>opstep \<alpha> ((sla + slb + sf, ss), ca \<parallel> cb) ((slf', ss'), c')\<close>
      \<open>F (sf, ss)\<close>

    have disjoint_parts:
      \<open>sla ## sf\<close>
      \<open>slb ## sf\<close>
      using Suc.prems(3) assms2(1)
      by (force dest: disjoint_add_leftL disjoint_add_leftR)+

    have framed_invs:
      \<open>(Ib \<^emph>\<and> F) (slb + sf, ss)\<close>
      \<open>(Ia \<^emph>\<and> F) (sla + sf, ss)\<close>
      using assms2(3) safe_suc1(3) safe_suc2(3)
      by (meson disjoint_parts(1-2) sepconj_conjI)+

    note safe_suc_step1 =
      safe_suc1(5)[OF
        disjoint_add_swap_lr[OF Suc.prems(3) assms2(1)] _ framed_invs(1),
        simplified refl, OF _ TrueI]
    note safe_suc_step2 =
      safe_suc2(5)[OF
        disjoint_add_swap_lr[OF
          disjoint_sym[OF Suc.prems(3)]
          assms2(1)[simplified partial_add_commute[OF Suc.prems(3)]]]
        _ framed_invs(2),
        simplified refl, OF _ TrueI]

    show \<open>\<alpha> \<noteq> Tau \<longrightarrow> (Ga \<squnion> Gb) ss ss'\<close>
      using Suc.prems(3) assms2 disjoint_parts safe_suc_step1 safe_suc_step2
      by (clarsimp simp del: sup_apply,
          metis disjoint_add_swap_lr disjoint_sym_iff partial_add_assoc3
          partial_add_assoc_commute_left)

    show \<open>\<exists>sl'.
            sl' ## sf \<and>
            slf' = sl' + sf \<and>
            (\<alpha> = Tau \<longrightarrow> sl' = sla + slb) \<and>
            safe R F (Ga \<squnion> Gb)
              (sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib)
              (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb)
              n c' (sl', ss')\<close>
      using Suc.prems(3) assms2 safe_suc1(1) safe_suc2(1)
      apply (simp add: del: sup_apply)
      apply (elim disjE conjE exE)
        (* subgoal: crash left *)
          apply blast
        (* subgoal: crash right *)
         apply blast
        (* subgoal: terminated *)
        apply (clarsimp simp del: sup_apply)
        apply (rule safe_term')
         apply (rule predicate1D[OF wlp_rely_sepconj_conj_semidistrib])
         apply (metis safe_suc1(2) safe_suc2(2) sepconj_conjI sup.cobounded1
          wssa_over_sswa_eq)
        apply (rule predicate1D[OF wlp_rely_sepconj_conj_semidistrib])
        apply (metis safe_suc1(3) safe_suc2(3) sepconj_conjI sswa_trivial sup_ge1
          wssa_over_sswa_eq)
        (* subgoal: left *)
       apply (simp add: partial_add_assoc2[of sla] del: sup_apply)
       apply (frule safe_suc_step1)
       apply (clarsimp simp del: sup_apply)
       apply (rule_tac x=\<open>sl' + slb\<close> in exI)
       apply (intro conjI)
          apply (metis disjoint_add_leftR disjoint_add_swap_rl)
         apply (metis disjoint_add_leftR partial_add_assoc3)
        apply blast
       apply (subgoal_tac \<open>sswa (R \<squnion> Ga) Ib (slb, ss')\<close>)
        prefer 2
        apply (cut_tac safe_suc2(3))
        apply (erule opstep_act_cases)
         apply force
        apply (metis (full_types) unit.exhaust sswa_step sswa_trivial sup2I2)
       apply (rule Suc.hyps[where slb=slb])
         apply blast
        apply (erule opstep_act_cases)
         apply (clarsimp simp del: sup_apply)
         apply (meson Suc.prems(2) safe_step_SucD; fail)
        apply (clarsimp simp del: sup_apply)
        apply (metis safe_suc2(4) split_pairs sup2CI)
       apply (metis disjoint_add_leftR disjoint_add_rightL)
        (* subgoal right *)
      apply (simp add: partial_add_commute[of sla] partial_add_assoc2[of slb]
          disjoint_sym_iff del: sup_apply)
      apply (frule safe_suc_step2)
      apply (clarsimp simp del: sup_apply)
      apply (rule_tac x=\<open>sla + sl'\<close> in exI)
      apply (intro conjI)
         apply (metis disjoint_parts(1) disjoint_add_right_commute2 disjoint_sym)
        apply (metis disjoint_parts(1) disjoint_add_rightL partial_add_assoc3 partial_add_commute)
       apply (blast dest: partial_add_commute)
      apply (subgoal_tac \<open>sswa (R \<squnion> Gb) Ia (sla, ss')\<close>)
       prefer 2
       apply (cut_tac safe_suc1(3))
       apply (erule opstep_act_cases)
        apply force
       apply (metis (full_types) unit.exhaust sswa_stepD sswa_trivial sup2I2)
      apply (rule Suc.hyps[where sla=sla])
        apply (erule opstep_act_cases)
         apply (clarsimp simp del: sup_apply)
         apply (metis Suc.prems(1) safe_step_SucD)
        apply (clarsimp simp del: sup_apply)
        apply (metis safe_suc1(4) fst_conv snd_conv sup2CI)
       apply (blast intro: safe_suc1(3))
      apply (metis disjoint_add_rightL disjoint_parts(1) disjoint_sym_iff)
      done
  qed
qed blast

lemma safe_parallel:
  \<open>safe (R \<squnion> Gb) (Ib \<^emph>\<and> F) Ga Ia (sswa (R \<squnion> Gb) qa) n ca (sla, ss) \<Longrightarrow>
    safe (R \<squnion> Ga) (Ia \<^emph>\<and> F) Gb Ib (sswa (R \<squnion> Ga) qb) n cb (slb, ss) \<Longrightarrow>
    sla ## slb \<Longrightarrow>
    sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb \<le> q \<Longrightarrow>
    sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib \<le> I \<Longrightarrow>
    Ga \<squnion> Gb \<le> G \<Longrightarrow>
    safe R F G I q n (ca \<parallel> cb) (sla + slb, ss)\<close>
  using safe_parallel' safe_mono[OF order.refl order.refl _ _ _ order.refl]
  by meson


subsection \<open> Safety of conj \<close>

lemma safe_conj:
  \<open>safe R F G I qa n c s \<Longrightarrow>
    safe R F G I qb n c s \<Longrightarrow>
    \<forall>z a b c. F (c,z) \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    safe R F G I (qa \<sqinter> qb) n c s\<close>
proof (induct n arbitrary: c s qa qb)
  case (Suc n)
  show ?case
    using Suc.prems
    apply -
    apply (intro safe_suc conjI impI allI)
         apply blast
        apply blast
       apply blast
      apply (rule Suc.hyps; blast)
      (* subgoal: frame safe *)
     apply (clarsimp simp del: inf_apply)
     apply (frule safe_sucD(5)[where q=qa], blast, blast, blast, force)
     apply (frule safe_sucD(5)[where q=qb], blast, blast, blast, force)
     apply force
    apply (frule(3) safe_sucD(5)[where q=qa], force)
    apply (frule(3) safe_sucD(5)[where q=qb], force)
    apply (clarsimp simp del: inf_apply)
    apply (metis Suc.hyps[of qa _ _ qb])
    done
qed blast


lemma safe_Conj':
  assumes frame_cancellative:
    \<open>\<forall>z a b f. F (f, z) \<longrightarrow> a ## f \<longrightarrow> b ## f \<longrightarrow> a + f = b + f \<longrightarrow> a = b\<close>
    and assms':
    \<open>Q \<noteq> {}\<close>
    \<open>\<forall>q\<in>Q. safe R F G I q n c s\<close>
  shows
    \<open>safe R F G I (\<Sqinter>Q) n c s\<close>
  using assms'
proof (induct n arbitrary: c s Q)
  case (Suc n)
  show ?case
    using Suc.prems
    apply (intro safe_suc)
      (* termination *)
       apply blast
      (* invariant *)
      apply blast
      (* rely step *)
     apply (rule Suc.hyps; blast)
      (* framed opstep *)
      (** split the post-state from the frame *)
    apply (subgoal_tac \<open>\<exists>q. q \<in> Q\<close>)
     prefer 2
     apply blast
    apply (clarsimp simp del: inf_apply Inf_apply)
    apply (frule bspec, assumption)
    apply (frule(3) safe_sucD(5), force)
    apply (clarsimp simp del: inf_apply Inf_apply)
      (** prove the goal *)
    apply (subgoal_tac \<open>\<forall>q\<in>Q. safe R F G I q n c' (sl', ss')\<close>)
     prefer 2
     apply clarsimp
     apply (metis frame_cancellative safe_sucD(5) surjective_pairing)
    apply (metis Suc.hyps)
    done
qed blast


section \<open> Soundness \<close>

lemma soundness:
  assumes \<open>rgsat c R G p q I F C\<close>
    and \<open>p s\<close>
    and \<open>C = \<top>\<close>
  shows \<open>safe R F G I q n c s\<close>
  using assms
proof (induct c R G p q I F C arbitrary: n s rule: rgsat.inducts)
  case (rgsat_skip p R q I C)
  then show ?case
    using safe_term[where p=p]
    by blast
next
  case (rgsat_iter c R G i I F C p q I')
  then show ?case
    apply -
    apply (rule safe_iter[where i=\<open>sswa R i\<close> and R=R, simplified])
      apply clarsimp
      apply (rule safe_mono_inv, assumption)
      apply (rule safe_mono_post[OF sswa_weaker])
      apply blast+
    done
next
  case (rgsat_seq ca r g p pp Ia F C cb q Ib I)
  then show ?case
    by (blast intro: safe_seq)
next
  case (rgsat_indet ca r ga p qa Ia F C cb gb qb Ib g q I)
  then show ?case
    by (blast intro!: safe_indet[where Ia=Ia and Ib=Ib]
        intro: safe_mono[OF order.refl order.refl _ order.refl _ order.refl])
next
  case (rgsat_endet c1 r Ga p qa Ia F C c2 Gb qb Ib g q I)
  then show ?case
    by (blast intro!: safe_endet[where Ia=Ia and Ib=Ib]
        intro: safe_mono[OF order.refl order.refl _ order.refl _ order.refl])
next
  case (rgsat_par ca R Gb Ga pa qa Ia Ib F C cb pb qb G p q I)
  
  obtain lsa lsb where
    \<open>pa (lsa, snd s)\<close>
    \<open>pb (lsb, snd s)\<close>
    \<open>lsa ## lsb\<close>
    \<open>fst s = lsa + lsb\<close>
    using rgsat_par.hyps(7) rgsat_par.prems(1)
    by (fastforce simp add: le_fun_def sepconj_conj_apply)
  then show ?case
    using rgsat_par.prems(2) rgsat_par.hyps(5,6,8,9)
      safe_parallel[of R Gb Ib F Ga Ia qa n ca lsa \<open>snd s\<close> qb cb lsb,
        OF safe_mono_postD[OF rgsat_par.hyps(2) sswa_weaker]
        safe_mono_postD[OF rgsat_par.hyps(4) sswa_weaker]]
    by (cases s, simp)
next
  case (rgsat_atom p' R p q q' I F ap aq G C)
  then show ?case
    by (intro safe_atom; simp add: rel_restr_fst_galois; blast)
next
  case (rgsat_frame c R G p q I F C p' f q' F' I')
  then show ?case
    apply -
    apply (frule(1) predicate1D)
    apply (clarsimp simp del: top_apply simp add: sepconj_conj_apply)
    apply (rule safe_frame[of R F G I q _ c _ _ f])
          apply blast
         apply assumption
        apply assumption
       apply (cases s, force)
      apply (simp add: sepimp_conj_sepconj_conj_shunt; fail)
     apply (simp add: sepimp_conj_sepconj_conj_shunt; fail)
    apply blast
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
  case (rgsat_Conj Q c R G p I F C q')
  then show ?case
    using safe_Conj'[of _ Q] safe_mono_postD[where q=\<open>\<Sqinter>Q\<close> and s=s and q'=q']
    by metis
qed

end