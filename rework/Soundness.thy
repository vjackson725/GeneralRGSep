theory Soundness
  imports RGLogic
begin

section \<open> Operational Semantics \<close>

type_synonym 's pconfig = \<open>'s \<times> 's comm\<close>

subsection \<open> Actions \<close>

datatype act = Tau | Vis

lemma act_not_eq_iff[simp]:
  \<open>\<alpha> \<noteq> Tau \<longleftrightarrow> \<alpha> = Vis\<close>
  \<open>\<alpha> \<noteq> Vis \<longleftrightarrow> \<alpha> = Tau\<close>
  by (meson act.distinct act.exhaust)+

lemma ex_act_neq[simp]:
  \<open>\<exists>\<alpha>. \<alpha> \<noteq> Vis\<close>
  \<open>\<exists>\<alpha>. \<alpha> \<noteq> Tau\<close>
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
        \<not> p (fst s, fst (snd s)) \<and> snd (snd (fst sc')) = Crashed) \<or>
      snd (snd s) = Crashed \<and> s = fst sc')\<close>
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
  state invariant \<open>I\<close> and all local steps must fulfil the guarantee condition \<open>G\<close>. In addition,
  the execution must always finish by terminating (not crashing), and uphold the postcondition \<open>q\<close>.
\<close>
inductive safe
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow>
      ('l::pre_perm_alg \<times> 's) comm \<Rightarrow>
      'l \<times> 's \<Rightarrow>
      bool\<close>
  for R G q
  where
  safe_nil[intro!]: \<open>safe R G q 0 c s\<close>
| safe_suc[intro]:
  \<open>\<comment> \<open> If the command is Skip, the postcondition is established.
        Note: this semantics represents termination by infinite final stuttering. \<close>
    c = Skip \<longrightarrow> q s \<Longrightarrow>
    \<comment> \<open> the current state obeys the state invariant \<close>
    \<comment> \<open> rely steps are safe \<close>
    (\<And>ss'. R (snd s) ss' \<Longrightarrow> safe R G q n c (fst s, ss')) \<Longrightarrow>
    \<comment> \<open> safe after opsteps \<close>
    (\<And>\<alpha> s' c'.
        (s, c) \<midarrow>\<alpha>\<rightarrow> (s', c') \<Longrightarrow>
        \<comment> \<open> Non-tau steps establish the guarantee. \<close>
        (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) (snd s')) \<and>
        \<comment> \<open> Tau moves are not allowed to change the state. \<close>
        (\<alpha> = Tau \<longrightarrow> fst s' = fst s) \<and> 
        safe R G q n c' s') \<Longrightarrow>
    \<comment> \<open> safe after framed opsteps \<close>
    (\<And>f \<alpha> slf' ss' c'.
        fst s ## f \<Longrightarrow>
        ((fst s + f, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((slf', ss'), c') \<Longrightarrow>
        \<comment> \<open> Non-tau steps establish the guarantee. \<close>
        (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) ss') \<and>
        \<comment> \<open> Note the existential! We only guarantee \<^emph>\<open>one\<close> such unframed state is safe.
             This is only relevant for non-cancellative frame, in which case the states in question
              are a verification fiction anyway, so this is reasonable. \<close>
        (\<exists>sl'.
          sl' ## f \<and>
          slf' = sl' + f \<and>
          (\<alpha> = Tau \<longrightarrow> sl' = fst s) \<and> \<comment> \<open> Tau moves are not allowed to change the fictive state! \<close>
          safe R G q n c' (sl', ss'))) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe R G q (Suc n) c s\<close>


subsection \<open> Proofs about safe \<close>

inductive_cases safe_zeroE[elim!]: \<open>safe R G q 0 c s\<close>
inductive_cases safe_sucE[elim]: \<open>safe R G q (Suc n) c s\<close>


lemma safe_nil_iff[simp]:
  \<open>safe R G q 0 c s\<close>
  by force

lemma safe_suc_iff:
  \<open>safe R G q (Suc n) c s \<longleftrightarrow>
    (c = Skip \<longrightarrow> q s) \<and>
    (\<forall>ss'. R (snd s) ss' \<longrightarrow> safe R G q n c (fst s, ss')) \<and>
    (\<forall>\<alpha> s' c'.
        ((fst s, snd s), c) \<midarrow>\<alpha>\<rightarrow> (s', c') \<longrightarrow>
          (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) (snd s')) \<and>
          (\<alpha> = Tau \<longrightarrow> fst s' = fst s) \<and>
          safe R G q n c' s') \<and>
    (\<forall>f \<alpha> slf' ss' c'.
        fst s ## f \<longrightarrow>
        ((fst s + f, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((slf', ss'), c') \<longrightarrow>
        (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) ss') \<and>
        (\<exists>sl'.
          sl' ## f \<and>
          slf' = sl' + f \<and>
          (\<alpha> = Tau \<longrightarrow> sl' = fst s) \<and>
          safe R G q n c' (sl', ss')))\<close>
  apply (rule iffI)
   apply (elim safe_sucE; simp; fail)
  apply (cases s, simp, rule safe_suc; force)
  done

lemma safe_sucD:
  \<open>safe R G q (Suc n) c s \<Longrightarrow> c = Skip \<Longrightarrow> q s\<close>
  \<open>safe R G q (Suc n) c s \<Longrightarrow> R ss ss' \<Longrightarrow> ss = snd s \<Longrightarrow> safe R G q n c (fst s, ss')\<close>
  \<open>safe R G q (Suc n) c s \<Longrightarrow>
    (s, c) \<midarrow>\<alpha>\<rightarrow> (s', c') \<Longrightarrow>
    (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) (snd s')) \<and>
    (\<alpha> = Tau \<longrightarrow> fst s' = fst s) \<and>
    safe R G q n c' s'\<close>
  \<open>safe R G q (Suc n) c s \<Longrightarrow>
    sl ## f \<Longrightarrow>
    ((sl + f, ss), c) \<midarrow>\<alpha>\<rightarrow> ((slf', ss'), c') \<Longrightarrow>
    s = (sl, ss) \<Longrightarrow>
    (\<alpha> \<noteq> Tau \<longrightarrow> G ss ss') \<and>
    (\<exists>sl'.
      sl' ## f \<and>
      slf' = sl' + f \<and>
      (\<alpha> = Tau \<longrightarrow> sl' = sl) \<and>
      safe R G q n c' (sl', ss'))\<close>
  by (erule safe_sucE; simp)+


subsubsection \<open> Monotonicity of safe \<close>

lemma safe_monoD:
  \<open>safe R G q n c s \<Longrightarrow>
    R' \<le> R \<Longrightarrow>
    G \<le> G' \<Longrightarrow>
    q \<le> q' \<Longrightarrow>
    m \<le> n \<Longrightarrow>
    safe R' G' q' m c s\<close>
  apply (induct m arbitrary: n c s)
   apply force
  apply (clarsimp simp add: safe_suc_iff Suc_leq_iff)
  apply (intro conjI)
    (* subgoal: post-condition *)
     apply (meson predicate1D; fail)
    (* subgoal: rely step *)
    apply blast
    (* subgoal: opstep *)
   apply (metis predicate2D)
    (* subgoal: framed opstep *)
  apply clarsimp
  apply (drule spec, drule mp[of \<open>_ ## _\<close>], assumption)
  apply (metis (full_types) predicate2D)
  done

lemmas safe_mono = safe_monoD[rotated]

lemmas safe_mono_stepsD = safe_monoD[OF _ order.refl order.refl order.refl]
lemmas safe_mono_steps = safe_mono_stepsD[rotated]

lemmas safe_mono_postD = safe_monoD[OF _ order.refl order.refl _ order.refl]
lemmas safe_mono_post = safe_mono_postD[rotated]

lemmas safe_mono_guarD = safe_monoD[OF _ order.refl _ order.refl order.refl]
lemmas safe_mono_guar = safe_mono_guarD[rotated]

lemmas safe_mono_relyD = safe_monoD[OF _ order.refl order.refl _ order.refl]
lemmas safe_mono_rely = safe_mono_relyD[rotated]


lemma safe_step_SucD:
  \<open>safe R G q (Suc n) c s \<Longrightarrow> safe R G q n c s\<close>
  by (metis safe_mono_stepsD le_add2 plus_1_eq_Suc)


subsection \<open> Safety of Skip \<close>

lemma safe_skip_iff:
  \<open>safe R G q n Skip s \<longleftrightarrow>
    (\<exists>sl ss. s = (sl, ss) \<and> (\<forall>k<n. \<forall>ss'. (R^^k) ss ss' \<longrightarrow> q (sl, ss')))\<close>
  apply (induct n arbitrary: s)
   apply (simp; fail)
  apply (rule iffI)
   apply (erule safe_sucE)
   apply (clarsimp simp add: less_Suc_eq_0_disj)
   apply (metis relpowp_Suc_D2')
  apply (simp add: safe_suc_iff)
  apply (metis Suc_mono prod_eq_decompose(2) relpowp_0_I relpowp_Suc_I2 zero_less_Suc)
  done

lemma safe_skip_stable_iff:
  assumes
    \<open>sswa R q \<le> q\<close>
  shows
    \<open>safe R G q n Skip s \<longleftrightarrow>
      (\<exists>hl hs. s = (hl, hs) \<and> (0 < n \<longrightarrow> q (hl, hs)))\<close>
proof -
  have \<open>\<And>n' hl hs. (\<forall>k\<le>n'. \<forall>hs'. (R ^^ k) hs hs' \<longrightarrow> q (hl, hs')) \<longleftrightarrow> q (hl, hs)\<close>
    using assms
    apply (simp add: le_fun_def sp_def imp_ex_conjL rtranclp_power)
    apply (metis le0 relpowp_0_I)
    done
  then show ?thesis
    apply (cases n, force)
    apply (rule trans[OF safe_skip_iff])
    apply (clarsimp simp add: less_Suc_eq_le)
    done
qed

lemma safe_skip':
  \<open>wssa R q s \<Longrightarrow> safe R G q n Skip s\<close>
  apply (induct n arbitrary: s)
   apply force
  apply (force simp add: wssa_step del: safe_suc intro!: safe_suc)
  done

lemma safe_skip:
  \<open>p s \<Longrightarrow> p \<le> wssa R q \<Longrightarrow> safe R G q n Skip s\<close>
  by (blast intro: safe_skip'[where q=\<open>q\<close>])


subsection \<open> Safety of frame \<close>

lemma safe_frame':
  \<open>safe R G q n c s \<Longrightarrow>
    s = (sl, ss) \<Longrightarrow>
    sl ## sf \<Longrightarrow>
    sswa (R \<squnion> G) F' (sf, ss) \<Longrightarrow>
    safe R G (q \<^emph>\<and> sswa (R \<squnion> G) F') n c (sl + sf, ss)\<close>
proof (induct arbitrary: sl ss sf rule: safe.induct)
  case (safe_nil c s)
  then show ?case by (metis safe.safe_nil)
next
  case (safe_suc c s n)

  note hyps = safe_suc.hyps[simplified safe_suc.prems(1)[simplified] fst_conv snd_conv]

  show ?case
    using safe_suc.prems
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: post-condition *)
       apply (cut_tac hyps(1))
       apply (force simp add: sepconj_conj_def simp del: sup_apply)
      (* subgoal: rely step *)
      apply (simp del: sup_apply)
      apply (metis hyps(3)  sswa_stepD sup2CI)
      (* subgoal: opstep *)
     apply (clarsimp simp del: sup_apply)
     apply (drule(1) hyps(5))
     apply (clarsimp simp del: sup_apply)
     apply (erule opstep_act_cases, force)
     apply (metis sswa_step sup2I2)
      (* subgoal: framed opstep *)
    apply (clarsimp simp add: partial_add_assoc2[of sl sf] simp del: sup_apply)
    apply (frule hyps(5)[rotated 1])
     apply (metis disjoint_add_swap_lr)
    apply (clarsimp simp del: sup_apply)
    apply (rule_tac x=\<open>sl' + sf\<close> in exI, rule conjI)
     apply (metis disjoint_add_leftR disjoint_add_swap_rl)
    apply (rule conjI)
      (** subgoal: guarantee *)
     apply (metis disjoint_add_leftR partial_add_assoc3)
      (** subgoal: safe preservation *)
    apply (clarsimp simp del: sup_apply)
    apply (erule opstep_act_cases, force)
    apply (metis sswa_stepD sup2I2 disjoint_add_leftR disjoint_add_rightL)
    done
qed

lemma safe_frame:
  \<open>safe R G q n c (sl, ss) \<Longrightarrow>
    F (sf, ss) \<Longrightarrow>
    sl ## sf \<Longrightarrow>
    s' = (sl + sf, ss) \<Longrightarrow>
    q \<^emph>\<and> sswa (R \<squnion> G) F \<le> q' \<Longrightarrow>
    safe R G q' n c s'\<close>
  by (simp add: safe_frame' safe_mono_post sswa_trivial)


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
  \<open>wssa R p s \<Longrightarrow>
    sp ar p \<le> q \<Longrightarrow>
    safe R
      (rel_restr_fst (rel_liftL (p \<squnion> p \<^emph>\<and> \<top>) \<sqinter> ar)) \<comment> \<open> G \<close>
      (sswa R q) \<comment> \<open> q \<close>
      n \<langle>ar\<rangle> s\<close>
proof (induct n arbitrary: s)
  case (Suc n)
  show ?case
    using Suc.prems
    apply -
    apply (cases s)
    apply (rename_tac sl ss)
    apply (clarsimp simp del: sup_apply inf_apply top_apply rel_lift_apply)
    apply (rule safe_suc)
      (* subgoal: post-condition *)
      apply force
      (* subgoal: rely step *)
      apply (metis Suc.hyps fst_conv snd_conv wssa_stepD)
      (* subgoal: opstep *)
     apply (simp del: inf_apply top_apply rel_lift_apply)
     apply (rule conjI)
      apply (force simp add: rel_restr_fst_def)
     apply (force simp add: safe_skip_stable_iff)
      (* subgoal: framed opstep *)
    apply (rule conjI)
      (* subsubgoal: guarantee *)
     apply (clarsimp simp add: rel_restr_fst_def simp del: top_apply)
     apply (metis sepconj_conjI top1I wssa_trivial)
      (* subsubgoal: safety after opstep *)
    apply (simp del: sup_apply top_apply inf_apply rel_lift_apply)
    apply (subgoal_tac \<open>sswa R (wssa R p \<squnion> sswa R q) \<le> wssa R p \<squnion> sswa R q\<close>)
     prefer 2
     apply (simp add: sp_sup; fail)
    apply (clarsimp simp add: safe_skip_stable_iff simp del: sup_apply inf_apply top_apply
        rel_lift_apply)
    apply (clarsimp simp add: sp_def[of ar] le_fun_def imp_ex_conjL)
    subgoal sorry
    done
qed fast

lemma safe_atom:
  \<open>rel_restr_fst (rel_liftL (p \<squnion> p \<^emph>\<and> \<top>) \<sqinter> ar) \<le> G \<Longrightarrow>
    wssa R p s \<Longrightarrow>
    sswa R q \<le> q' \<Longrightarrow>
    safe R G q' n \<langle>ar\<rangle> s\<close>
  sorry
(*
  apply (rule safe_monoD[OF _ order.refl order.refl _ _ _ order.refl, rotated])
     apply assumption
    apply (rule sup_least[of \<open>wssa R p\<close> _ \<open>sswa R q\<close>]; assumption)
   apply assumption
  apply (rule safe_atom'; fast)
  done
*)


subsection \<open> Safety of Sequencing \<close>

lemma safe_seq_assoc_left:
  \<open>safe R G q n c s \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe R G q n ((c1 ;; c2) ;; c3) s\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
     apply blast
    apply blast
  subgoal sorry
  subgoal sorry
  done

lemma safe_seq_assoc_right:
  \<open>safe R G q n c s \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    safe R G q n (c1 ;; c2 ;; c3) s\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
     apply blast
    apply blast
  subgoal sorry
  subgoal sorry
  done

lemma safe_seq':
  \<open>safe R Ga q n ca s \<Longrightarrow>
    (\<forall>m\<le>n. \<forall>s'. q s' \<longrightarrow> safe R Gb q' m cb s') \<Longrightarrow>
    safe R G q' n (ca ;; cb) s\<close>
proof (induct arbitrary: cb q' rule: safe.inducts)
  case (safe_suc c s n)

  have safe_c2:
    \<open>\<And>m s'. m \<le> n \<Longrightarrow> q s' \<Longrightarrow> safe R Gb q' m cb s'\<close>
    \<open>\<And>s'. q s' \<Longrightarrow> safe R Gb q' (Suc n) cb s'\<close>
    by (simp add: safe_suc.prems[simplified fst_conv snd_conv])+
  then show ?case
    using safe_suc.prems(1) safe_suc.hyps(1)
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
        apply force
      (* subgoal: rely *)
      apply (metis safe_suc.hyps(3))
      (* subgoal: opstep *)
    subgoal sorry
      (* subgoal: framed opstep *)
    subgoal sorry
        (*
    apply (clarsimp simp del: sup_apply)
    apply (elim disjE conjE exE)
      (** term *)
     apply clarsimp
     apply (meson order.refl inf_sup_ord(4) safe_c2(1) safe_monoD; fail)
      (** step *)
     apply (frule safe_suc.hyps(5))
    apply (metis act.distinct(1) safe_c2(1))
*)
    done
qed force

lemma safe_seq:
  \<open>safe R Ga q n ca s \<Longrightarrow>
    (\<forall>s'. q s' \<longrightarrow> safe R Gb q' n cb s') \<Longrightarrow>
    safe R G q' n (ca ;; cb) s\<close>
  subgoal sorry
(*
  apply (rule safe_monoD[where I=\<open>Ia \<squnion> Ib\<close>,
        OF _ order.refl order.refl order.refl _ order.refl order.refl])
   apply (rule safe_seq', blast)
   apply (meson order.refl safe_monoD; fail)
  apply force
*)
  done


subsection \<open> Safety of Iter \<close>

lemma safe_iter':
  \<open>\<forall>s'. wssa R i s' \<longrightarrow> safe R G (wssa R i) n c s' \<Longrightarrow>
    wssa R i s \<Longrightarrow>
    safe R G (wssa R i) n (Iter c) s\<close>
proof (induct n arbitrary: i s)
  case (Suc n)

  have safe_ih:
    \<comment> \<open> we never need to go back beyond \<open>n\<close> \<close>
    \<open>\<And>s'. wssa R i s' \<Longrightarrow> safe R G (wssa R i) n c s'\<close>
    \<open>\<And>s'. wssa R i s' \<Longrightarrow> safe R G (wssa R i) (Suc n) c s'\<close>
    using Suc.prems(1) safe_mono_steps[OF le_SucI[OF order.refl]]
    by blast+

  note safe_suc_c = safe_sucD[OF safe_ih(2)]

  show ?case
    using Suc.prems(2)
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
       apply blast
      (* subgoal: rely *)
     apply (rule Suc.hyps[where i=i])
      apply (simp add: safe_ih(1); fail)
      apply (simp add: wssa_step; fail)
(* subgoal: opstep *)
    subgoal sorry
      (* subgoal: framed opstep *)
    apply (simp add: le_fun_def del: split_paired_All)
    apply (rule conjI)
      (** guar *)
     apply (metis safe_suc_c(4) act.distinct(1) prod.collapse)
      (** step *)
    apply (elim disjE conjE exE)
      (*** loop-end *)
     apply simp
     apply (rule safe_skip')
     apply force
      (*** step *)
    subgoal sorry
(*
    apply (clarsimp simp add: safe_suc_iff simp del: split_paired_All)
    apply (rename_tac c')
    apply (frule(3) safe_suc_c(4), force)
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
*)
    done
qed force

lemma safe_iter:
  \<open>\<forall>s'. wssa R i s' \<longrightarrow> safe R G (wssa R i) n c s' \<Longrightarrow>
    wssa R i s \<Longrightarrow>
    wssa R i \<le> q' \<Longrightarrow>
    safe R G q' n (Iter c) s\<close>
  using safe_iter'
  by (metis (no_types, opaque_lifting) safe_mono_postD)


subsubsection \<open> Safety of internal nondeterminism \<close>

lemma safe_indet':
    \<open>safe R G q n ca s \<Longrightarrow>
      safe R G q n cb s \<Longrightarrow>
      safe R G q n (ca \<^bold>\<sqinter> cb) s\<close>
proof (induct n arbitrary: ca cb s)
  case (Suc n)

  show ?case
    using Suc.prems
    apply -
    apply (rule safe_suc)
      (* subgoal: rely *)
       apply blast
      (* subgoal: rely *)
     apply (rule Suc.hyps)
      apply (blast dest: safe_sucD)
      apply (blast dest: safe_sucD)
      (* subgoal: opstep *)
    subgoal sorry
        (* subgoal: framed opstep *)
    apply (clarsimp simp add: conj_disj_distribL[symmetric] simp del: sup_apply)
    apply (metis safe_step_SucD)
    done
qed blast

lemma safe_indet:
  \<open>safe R Ga q n ca s \<Longrightarrow>
    safe R Gb q n cb s \<Longrightarrow>
    Ga \<squnion> Gb \<le> G \<Longrightarrow>
    safe R G q n (ca \<^bold>\<sqinter> cb) s\<close>
  using safe_indet'
  by (metis le_supE safe_mono_guarD)


subsubsection \<open> Safety of external nondeterminism \<close>

lemma safe_endet':
  \<open>safe R G q n ca s \<Longrightarrow>
    safe R G q n cb s \<Longrightarrow>
    safe R G q n (ca \<^bold>\<box> cb) s\<close>
proof (induct n arbitrary: ca cb s)
  case (Suc n)
  show ?case
    using Suc.prems
    apply -
    apply (rule safe_suc)
      (* subgoal: skip *)
       apply blast
      (* subgoal: rely *)
      apply (rule Suc.hyps)
       apply (blast dest: safe_sucD)
      apply (blast dest: safe_sucD)
      (* subgoal: opstep *)
    subgoal sorry
        (* subgoal: frame opstep *)
    apply clarsimp
    apply (elim disjE conjE exE)
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
  \<open>safe R Ga q n ca s \<Longrightarrow>
    safe R Gb q n cb s \<Longrightarrow>
    Ga \<squnion> Gb \<le> G \<Longrightarrow>
    safe R G q n (ca \<^bold>\<box> cb) s\<close>
  using safe_endet'
  by (metis le_supE safe_mono_guar)


subsection \<open> Safety of parallel \<close>

lemma safe_parallel':
  \<open>safe (R \<squnion> Gb) Ga (sswa (R \<squnion> Gb) qa) n ca (sla, ss) \<Longrightarrow>
    safe (R \<squnion> Ga) Gb (sswa (R \<squnion> Ga) qb) n cb (slb, ss) \<Longrightarrow>
    sla ## slb \<Longrightarrow>
    safe R (Ga \<squnion> Gb)
      (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb)
      n (ca \<parallel> cb) (sla + slb, ss)\<close>
proof (induct n arbitrary: ca cb sla slb ss)
  case (Suc n)

  note safe_suc1 = safe_sucD[OF Suc.prems(1)]
  note safe_suc2 = safe_sucD[OF Suc.prems(2)]

  show ?case
  proof (rule safe_suc; fast?; (intro conjI)?; (simp only: fst_conv snd_conv)?)
    fix ss'
    assume \<open>R ss ss'\<close>
    then show
      \<open>safe R (Ga \<squnion> Gb) (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb) n (ca \<parallel> cb) (sla + slb, ss')\<close>
      using Suc.prems
      by (intro Suc.hyps; fastforce)
  next
    (* subgoal: opstep *)
next
    fix \<alpha> c' sf s'
    assume assms2:
      \<open>opstep \<alpha> ((sla + slb, ss), ca \<parallel> cb) (s', c')\<close>

    show \<open>\<alpha> \<noteq> Tau \<longrightarrow> (Ga \<squnion> Gb) ss (snd s')\<close>
      sorry
    show \<open>\<alpha> = Tau \<longrightarrow> fst s' = sla + slb\<close>
      sorry
    show \<open>safe R (Ga \<squnion> Gb) (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb) n c' s'\<close>
      using Suc.prems(3) assms2 safe_suc1(1) safe_suc2(1)
      apply (simp add: del: sup_apply)
      apply (elim disjE conjE exE)
        (* subgoal: terminated *)
        apply (clarsimp simp del: sup_apply)
        apply (rule safe_skip')
        apply (rule predicate1D[OF wlp_rely_sepconj_conj_semidistrib])
        apply (simp add: sepconj_conjI; fail)
        (* subgoal: left *)
       apply (simp del: sup_apply)
      subgoal sorry
          (* subgoal: right *)
      subgoal sorry
      done
  next
    (* subgoal: framed opstep *)
    fix \<alpha> c' sf slf' ss'
    assume assms2:
      \<open>sla + slb ## sf\<close>
      \<open>opstep \<alpha> ((sla + slb + sf, ss), ca \<parallel> cb) ((slf', ss'), c')\<close>

    have disjoint_parts:
      \<open>sla ## sf\<close>
      \<open>slb ## sf\<close>
      using Suc.prems(3) assms2(1)
      by (force dest: disjoint_add_leftL disjoint_add_leftR)+

    note safe_suc_step1 =
      safe_suc1(4)[OF disjoint_add_swap_lr[OF Suc.prems(3) assms2(1)] _,
        simplified refl]
    note safe_suc_step2 =
      safe_suc2(4)[OF disjoint_add_swap_lr[OF disjoint_sym[OF Suc.prems(3)]
                        assms2(1)[simplified partial_add_commute[OF Suc.prems(3)]]] _,
        simplified refl]

    show \<open>\<alpha> \<noteq> Tau \<longrightarrow> (Ga \<squnion> Gb) ss ss'\<close>
      using Suc.prems(3) assms2 disjoint_parts safe_suc_step1 safe_suc_step2
      by (clarsimp simp del: sup_apply,
          metis disjoint_add_swap_lr disjoint_sym_iff partial_add_assoc3
          partial_add_assoc_commute_left)

    show \<open>\<exists>sl'.
            sl' ## sf \<and>
            slf' = sl' + sf \<and>
            (\<alpha> = Tau \<longrightarrow> sl' = sla + slb) \<and>
            safe R (Ga \<squnion> Gb) (sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb) n c' (sl', ss')\<close>
      using Suc.prems(3) assms2 safe_suc1(1) safe_suc2(1)
      apply (simp add: del: sup_apply)
      apply (elim disjE conjE exE)
        (* subgoal: terminated *)
        apply (clarsimp simp del: sup_apply)
        apply (rule safe_skip')
         apply (rule predicate1D[OF wlp_rely_sepconj_conj_semidistrib])
        apply (simp add: sepconj_conjI; fail)
      subgoal sorry
(*
        apply (rule predicate1D[OF wlp_rely_sepconj_conj_semidistrib])
        apply (metis safe_suc1(2) safe_suc2(2) sepconj_conjI sswa_trivial sup_ge1
          wssa_over_sswa_eq)
*)
        (* subgoal: left *)
      apply (simp add: partial_add_assoc2[of sla] del: sup_apply)
subgoal sorry
(*
       apply (frule safe_suc_step1)
       apply (clarsimp simp del: sup_apply)
       apply (rule_tac x=\<open>sl' + slb\<close> in exI)
       apply (intro conjI)
          apply (metis disjoint_add_leftR disjoint_add_swap_rl)
         apply (metis disjoint_add_leftR partial_add_assoc3)
        apply blast
       apply (subgoal_tac \<open>sswa (R \<squnion> Ga) Ib (slb, ss')\<close>)
        prefer 2
        apply (cut_tac safe_suc2(2))
        apply (erule opstep_act_cases)
         apply force
        apply (metis (full_types) sswa_step sswa_trivial sup2I2)
       apply (rule Suc.hyps[where slb=slb])
         apply blast
        apply (erule opstep_act_cases)
         apply (clarsimp simp del: sup_apply)
         apply (meson Suc.prems(2) safe_step_SucD; fail)
        apply (clarsimp simp del: sup_apply)
        apply (metis safe_suc2(3) split_pairs sup2CI)
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
       apply (cut_tac safe_suc1(2))
       apply (erule opstep_act_cases)
        apply force
       apply (metis (full_types) sswa_stepD sswa_trivial sup2I2)
      apply (rule Suc.hyps[where sla=sla])
        apply (erule opstep_act_cases)
         apply (clarsimp simp del: sup_apply)
         apply (metis Suc.prems(1) safe_step_SucD)
        apply (clarsimp simp del: sup_apply)
        apply (metis safe_suc1(3) fst_conv snd_conv sup2CI)
       apply (blast intro: safe_suc1(3))
      apply (metis disjoint_add_rightL disjoint_parts(1) disjoint_sym_iff)
*)
      done
  qed
qed blast

lemma safe_parallel:
  \<open>safe (R \<squnion> Gb) Ga (sswa (R \<squnion> Gb) qa) n ca (sla, ss) \<Longrightarrow>
    safe (R \<squnion> Ga) Gb (sswa (R \<squnion> Ga) qb) n cb (slb, ss) \<Longrightarrow>
    sla ## slb \<Longrightarrow>
    sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb \<le> q \<Longrightarrow>
    Ga \<squnion> Gb \<le> G \<Longrightarrow>
    safe R G q n (ca \<parallel> cb) (sla + slb, ss)\<close>
  using safe_parallel'
  by (metis (full_types) safe_mono_guar safe_mono_rely)


subsection \<open> Safety of conj \<close>

lemma safe_conj:
  fixes s :: \<open>'l::pre_perm_alg \<times> 's\<close>
  shows
  \<open>safe R G qa n c s \<Longrightarrow>
    safe R G qb n c s \<Longrightarrow>
    \<forall>a b c::'l. a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    safe R G (qa \<sqinter> qb) n c s\<close>
proof (induct n arbitrary: c s qa qb)
  case (Suc n)
  show ?case
    using Suc.prems
    apply -
    apply (intro safe_suc)
      (* subgoal: post-condition *)
       apply blast
      (* subgoal: rely step *)
      apply (rule Suc.hyps; blast)
      (* subgoal: opstep *)
    subgoal sorry
        (* subgoal: framed opstep *)
    apply (clarsimp simp del: inf_apply)
    apply (frule(2) safe_sucD(4)[where q=qa], force)
    apply (frule(2) safe_sucD(4)[where q=qb], force)
    apply (clarsimp simp del: inf_apply)
    apply (metis Suc.hyps[of qa _ _ qb])
    done
qed blast


lemma safe_Conj':
  fixes s :: \<open>'l::pre_perm_alg \<times> 's\<close>
  assumes frame_cancellative:
    \<open>\<forall>a b f::'l. a ## f \<longrightarrow> b ## f \<longrightarrow> a + f = b + f \<longrightarrow> a = b\<close>
    and assms':
    \<open>Q \<noteq> {}\<close>
    \<open>\<forall>q\<in>Q. safe R G q n c s\<close>
  shows
    \<open>safe R G (\<Sqinter>Q) n c s\<close>
  using assms'
proof (induct n arbitrary: c s Q)
  case (Suc n)
  show ?case
    using Suc.prems
    apply (intro safe_suc)
      (* subgoal: termination *)
       apply blast
      (* subgoal: rely step *)
      apply (rule Suc.hyps; blast)
      (* subgoal: opstep *)
    subgoal sorry
        (* subgoal: framed opstep *)
        (** split the post-state from the frame *)
    apply (subgoal_tac \<open>\<exists>q. q \<in> Q\<close>)
     prefer 2
     apply blast
    apply (clarsimp simp del: inf_apply Inf_apply)
    apply (frule bspec, assumption)
    apply (frule(2) safe_sucD(4), force)
    apply (clarsimp simp del: inf_apply Inf_apply)
      (** prove the goal *)
    apply (subgoal_tac \<open>\<forall>q\<in>Q. safe R G q n c' (sl', ss')\<close>)
     prefer 2
     apply clarsimp
     apply (metis frame_cancellative safe_sucD(4) surjective_pairing)
    apply (metis Suc.hyps)
    done
qed blast


section \<open> Soundness \<close>

lemma
  \<open>(\<top> :: 'l::sep_alg \<times> 's \<Rightarrow> bool) \<^emph>\<and> \<top> = \<top>\<close>
  by (metis (no_types, opaque_lifting) predicate1I sepconj_conj_apply top.extremum_unique top1I zero_disjointR
      zero_unitR)

lemma soundness:
  assumes \<open>rgsat c R G p q I F C\<close>
    and \<open>p s\<close>
    and \<open>C = \<top>\<close>
    and \<open>F = \<top>\<close>
  shows \<open>safe R G q n c s\<close>
  using assms
proof (induct c R G p q I F C arbitrary: n s rule: rgsat.inducts)
  case (rgsat_skip p R q I C)
  then show ?case
    using safe_skip[where p=p]
    by blast
next
  case (rgsat_iter c R G i I F C p q)
  then show ?case
    apply -
    apply (rule safe_iter[where i=\<open>sswa R i\<close> and R=R, simplified])
      apply (clarsimp simp del: top_apply)
      apply (metis rgsat_iter.hyps(2) safe_mono_rely sswa_weaker)
     apply blast
    apply blast
    done
next
  case (rgsat_seq ca r g p pp Ia F C cb q Ib I)
  then show ?case
    by (blast intro: safe_seq)
next
  case (rgsat_indet ca r ga p qa Ia F C cb gb qb Ib g q I)
  then show ?case
    by (metis safe_indet' safe_mono_guar safe_mono_rely)
next
  case (rgsat_endet c1 r Ga p qa Ia F C c2 Gb qb Ib g q I)
  then show ?case
    by (metis safe_endet' safe_mono_guar safe_mono_rely)
next
  case (rgsat_par ca R Gb Ga pa qa Ia Ib F C cb pb qb G p q I)
  
  obtain lsa lsb ss where
    \<open>pa (lsa, ss)\<close>
    \<open>pb (lsb, ss)\<close>
    \<open>lsa ## lsb\<close>
    \<open>s = (lsa + lsb, ss)\<close>
    using rgsat_par.hyps(7) rgsat_par.prems(1)
    by (cases s, fastforce simp add: le_fun_def sepconj_conj_apply)
  then show ?case
    using rgsat_par.prems
    apply (simp del: top_apply)
    apply (rule safe_parallel[where Ga=Ga and Gb=Gb and qa=qa and qb=qb])
        apply (force intro: rgsat_par.hyps(2) safe_mono_postD)
       apply (force intro: rgsat_par.hyps(4) safe_mono_postD)
      apply blast
    apply (cut_tac rgsat_par.hyps(8))
    apply blast
    apply (simp add: rgsat_par.hyps(5,6))
    done
next
  case (rgsat_atom p' R p q q' I F ap aq G C)
  then show ?case
    apply (intro safe_atom; simp add: rel_restr_fst_galois del: top_apply)
    apply blast
    done
next
  case (rgsat_frame c R G p q I F C p' f q' F' I')
  then show ?case
    apply -
    apply (frule(1) predicate1D)
    apply (clarsimp simp del: top_apply simp add: sepconj_conj_apply)
    apply (rule safe_frame[where q=q and F=f])
        apply blast
       apply blast
      apply force
     apply (metis surjective_pairing)
    apply assumption
    done
next
  case (rgsat_weaken c R' G' p' q' I' F' C p q R G I F)
  moreover have \<open>p' s\<close>
    using rgsat_weaken.hyps(3) rgsat_weaken.prems
    by blast
  moreover then have \<open>safe R' G' q' n c s\<close>
    using rgsat_weaken.prems rgsat_weaken.hyps(3-)
    using rgsat_weaken.hyps(2) by blast
  ultimately show ?case
    by (meson order.refl safe_monoD)
next
  case rgsat_Disj
  then show ?case by fast
next
  case (rgsat_Conj Q c R G p I F C q')
  then show ?case
    using safe_Conj'[where Q=Q] safe_mono_postD[where q=\<open>\<Sqinter>Q\<close> and s=s and q'=q']
    by (metis top1I)
qed

end