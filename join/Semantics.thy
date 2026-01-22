theory Semantics
  imports SepLogic "../Lang"
begin

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


subsubsection \<open> Interaction with map_comm \<close>

lemma map_atom_step_preserved:
  \<open>(s, map_atom f c) \<midarrow>\<alpha>\<rightarrow> (s', cx') \<Longrightarrow> \<exists>c'. cx' = map_atom f c'\<close>
  apply (induct c arbitrary: cx')
        apply force
       apply clarsimp
       apply (metis map_atom.simps(2))
      apply clarsimp
      apply (elim disjE, metis; metis map_atom.simps(3))
     apply force
    apply clarsimp
    apply (elim disjE; blast?; metis map_atom.simps(5))
   apply clarsimp
   apply (metis map_atom.simps(1))
  apply clarsimp
  apply (metis map_atom.simps(1,2,7))
  done


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

paragraph \<open> Await \<close>

lemma opstep_await_iff[simp]:
  \<open>opstep \<alpha> (s, Await p) sc' \<longleftrightarrow>
    \<alpha> = Vis \<and> p s \<and> sc' = (s, Skip)\<close>
  by (cases sc', force simp add: await_rel_def)


paragraph \<open> IfThenElse \<close>

lemma opstep_IfThenElse_iff[simp]:
  \<open>opstep \<alpha> (s, IfThenElse p ct cf) sc' \<longleftrightarrow>
    \<alpha> = Vis \<and>
    (p s \<and> sc' = (s, Skip ;; ct) \<or>
      \<not> p s \<and> sc' = (s, Skip ;; cf))\<close>
  by (cases sc', force simp add: IfThenElse_def await_rel_def)

lemma opstep_WhileLoop_iff[simp]:
  \<open>opstep \<alpha> (h, WhileLoop p c) s' \<longleftrightarrow>
    \<alpha> \<noteq> Tau \<and> p h \<and> s' = (h, (Skip ;; c) ;; DO Await p ;; c OD) \<or>
    \<alpha> = Tau \<and> \<not> p h \<and> s' = (h, Skip)\<close>
  by (force simp add: WhileLoop_def await_rel_def pre_state_def)


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
  :: \<open>('s::join_alg \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 's comm \<Rightarrow> 's \<Rightarrow> bool\<close>
  for F I q
  where safeI[intro]:
    \<open>\<comment> \<open> If the command is Skip, the postcondition is established.
        Note: this semantics represents termination by infinite final stuttering. \<close>
    (c = Skip \<longrightarrow> q s) \<Longrightarrow>
    \<comment> \<open> the current state obeys the state invariant \<close>
    I s \<Longrightarrow>
    \<comment> \<open> Safe is closed under framed opsteps: \<close>
    (\<And>n' f sf \<alpha> sf' c'.
      n = Suc n' \<Longrightarrow>
      F f \<Longrightarrow>
      \<^bold>J s f sf \<Longrightarrow>
      (sf, c) \<midarrow>\<alpha>\<rightarrow> (sf', c') \<Longrightarrow>
        \<comment> \<open> Note the existential! We only guarantee \<^emph>\<open>one\<close> such unframed state is safe.
              When \<open>\<^bold>J\<close> is cancellative, there can only be one such state. \<close>
      (\<exists>s'. \<^bold>J s' f sf' \<and> 
        (\<alpha> = Tau \<longrightarrow> s' = s) \<and> \<comment> \<open> Tau moves are not allowed to change the state! \<close>
        safe F I q n' c' s')) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe F I q n c s\<close>


subsection \<open> Proofs about safe \<close>

inductive_cases safeE[elim]: \<open>safe F I q n c s\<close>
inductive_cases safe_zeroE[elim!]: \<open>safe F I q 0 c s\<close>
lemmas safe_sucE[elim] = safeE[where n=\<open>Suc n'\<close> for n', simplified]

lemma safe_then_state_inv:
  assumes \<open>safe F I q n c s\<close>
  shows \<open>I s\<close>
  using assms
  by (induct rule: safe.inducts) blast+

lemma safe_then_postcond:
  assumes \<open>safe F I q n c s\<close>
  shows \<open>c = Skip \<longrightarrow> q s\<close>
  using assms
  by (induct rule: safe.inducts) blast+

lemma safe_suc_then_step:
  \<open>safe F I q (Suc n') c s \<Longrightarrow>
    F f \<Longrightarrow>
    \<^bold>J s f sf \<Longrightarrow>
    (sf, c) \<midarrow>\<alpha>\<rightarrow> (sf', c') \<Longrightarrow>
    (\<exists>s'. \<^bold>J s' f sf' \<and> 
      (\<alpha> = Tau \<longrightarrow> s' = s) \<and>
      safe F I q n' c' s')\<close>
  by blast


lemma safe_nil_iff[simp]:
  \<open>safe F I q 0 c s \<longleftrightarrow> (c = Skip \<longrightarrow> q s) \<and> I s\<close>
  by blast

lemma safe_suc_iff:
  \<open>safe F I q (Suc n) c s \<longleftrightarrow>
    (c = Skip \<longrightarrow> q s) \<and>
    I s \<and>
    (\<forall>f sf \<alpha> s'f c'.
      F f \<longrightarrow>
      \<^bold>J s f sf \<longrightarrow>
      (sf, c) \<midarrow>\<alpha>\<rightarrow> (s'f, c') \<longrightarrow>
      (\<exists>s'. \<^bold>J s' f s'f \<and> (\<alpha> = Tau \<longrightarrow> s' = s) \<and> safe F I q n c' s'))\<close>
  by auto


subsection \<open> Monotonicity of safe \<close>

lemma safe_monoD:
  \<open>safe F I q n c s \<Longrightarrow>
    F' \<le> F \<Longrightarrow>
    I \<le> I' \<Longrightarrow>
    q \<le> q' \<Longrightarrow>
    m \<le> n \<Longrightarrow>
    safe F' I' q' m c s\<close>
proof (induct arbitrary: m rule: safe.induct)
  case (safeI c s n)

  show ?case
  proof (rule safe.safeI)
    show \<open>c = Skip \<longrightarrow> q' s\<close>
      using safeI by auto
  next
    show \<open>I' s\<close>
      using safeI by auto
  next
    fix m' f sf \<alpha> sf' c'
    assume assms2:
      \<open>m = Suc m'\<close>
      \<open>(sf, c) \<midarrow>\<alpha>\<rightarrow> (sf', c')\<close>
      \<open>\<^bold>J s f sf\<close>
      \<open>F' f\<close>
    then obtain n' where n_eqns:
      \<open>n = Suc n'\<close>
      \<open>m' \<le> n'\<close>
      using safeI.prems Suc_leq_iff
      by blast
    have fs_in_F: \<open>F f\<close>
      using assms2(4) safeI.prems(1) by auto
    then show
      \<open>\<exists>s'. \<^bold>J s' f sf' \<and> (\<alpha> = Tau \<longrightarrow> s' = s) \<and> safe F' I' q' m' c' s'\<close>
      using assms2(2-3) n_eqns(1-2) safeI.hyps(3) safeI.prems(1-3)
      by blast
  qed
qed

lemmas safe_mono = safe_monoD[rotated]

lemmas safe_mono_stepsD = safe_monoD[OF _ order.refl order.refl order.refl]
lemmas safe_mono_steps = safe_mono_stepsD[rotated]

lemmas safe_mono_invD = safe_monoD[OF _ order.refl _ order.refl order.refl]
lemmas safe_mono_inv = safe_mono_invD[rotated]

lemmas safe_mono_postD = safe_monoD[OF _ order.refl order.refl _ order.refl]
lemmas safe_mono_post = safe_mono_postD[rotated]

lemmas safe_mono_frameD = safe_monoD[OF _ _ order.refl order.refl order.refl]
lemmas safe_mono_frame = safe_mono_frameD[rotated]

lemma safe_step_SucD:
  \<open>safe F I q (Suc n) c s \<Longrightarrow> safe F I q n c s\<close>
  by (metis safe_mono_stepsD le_add2 plus_1_eq_Suc)


subsection \<open> Safety of Skip \<close>

lemma safe_skip_iff[simp]:
  \<open>safe F I q n Skip s \<longleftrightarrow> q s \<and> I s\<close>
  by auto


subsection \<open> Safety of frame \<close>

lemma safe_frame:
  \<open>safe (F \<^emph> Fy) I q n c s \<Longrightarrow>
    \<^bold>J s y sy \<Longrightarrow>
    Fy y \<Longrightarrow>
    safe F (I \<^emph> Fy) (q \<^emph> Fy) n c sy\<close>
proof (induct arbitrary: y sy rule: safe.induct)
  case (safeI c s n)

  note nice_hyps = safeI.hyps[simplified safeI.prems(1)[simplified] fst_conv snd_conv]

  show ?case
    using safeI.prems(1-2) nice_hyps(1-2)
    apply -
    apply (rule safe.safeI)
      (* subgoal: skip *)
      apply (simp add: sepconjI; fail)
      (* subgoal: stateset *)
     apply (simp add: sepconjI; fail)
      (* subgoal: framed opstep *)
    apply (rename_tac n' f syf \<alpha> syf' c')
    apply (subgoal_tac \<open>\<exists>yf. \<^bold>J y f yf \<and> \<^bold>J s yf syf\<close>)
     prefer 2
     apply (blast dest: join_assoc)
    apply clarsimp
    apply (frule nice_hyps(3))
       apply (rule_tac c=yf in sepconj_commI; assumption)
      apply fast
     apply fast
    apply clarsimp
    apply (subgoal_tac \<open>\<exists>s'y. \<^bold>J s' y s'y \<and> \<^bold>J s'y f syf'\<close>)
     prefer 2
     apply (metis join_assoc2 join_comm)
    apply clarsimp
    apply (metis fstI opstep_tau_preserves_heap)
    done
qed


subsection \<open> Safety of Atomic \<close>

lemma safe_atom:
  \<open>\<forall>f\<le>F. sp a (p \<^emph> f) \<le> q \<^emph> f \<Longrightarrow> p s \<Longrightarrow> safe F (p \<squnion> q) q n \<langle>a\<rangle> s\<close>
proof (induct n arbitrary: s)
  case (Suc n)
  note ih = Suc.hyps[simplified fst_conv snd_conv]
  show ?case
    using Suc.prems
    apply -
    apply (rule safeI)
      (* subgoal: termination *)
      apply fast
      (* subgoal: state inv *)
     apply fast
      (* subgoal: framed opstep *)
    apply (clarsimp simp add: sp_def le_fun_def imp_ex_conjL imp_conjL sepconj_def)
    apply (drule_tac x=\<open>(=) f\<close> in spec, drule mp, fast)
    apply blast
    done
qed simp


subsection \<open> Safety of Sequencing \<close>

lemma safe_seq_assoc_left:
  \<open>safe F I q n c s \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe F I q n ((c1 ;; c2) ;; c3) s\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
  apply (rule safeI)
    apply blast
   apply blast
  apply clarsimp
  apply (elim disjE; blast)
  done

lemma safe_seq_assoc_right:
  \<open>safe F I q n c s \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    safe F I q n (c1 ;; c2 ;; c3) s\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
  apply (rule safeI)
     apply blast
   apply blast
  apply clarsimp
  apply (elim disjE; blast)
  done

lemma safe_seq:
  \<open>safe F I q n ca s \<Longrightarrow>
    \<forall>s'. q s' \<longrightarrow> safe F I q' n cb s' \<Longrightarrow>
    safe F I q' n (ca ;; cb) s\<close>
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
      (* subgoal: local framed opstep *)
    apply (clarsimp simp del: sup_apply)
    apply (elim disjE conjE exE)
      (** left skip *)
     apply (metis safeI.prems safe_step_SucD)
      (** left step *)
    apply (frule(3) safeI.hyps(3))
    apply (metis safeI.prems safe_step_SucD)
    done
qed


subsection \<open> Safety of Iter \<close>

lemma safe_iter:
  \<open>i \<le> safe F I i n c \<Longrightarrow> i s \<Longrightarrow> safe F I i n (Iter c) s\<close>
proof (induct n arbitrary: i s)
  case (Suc n)

  have safe_n_c:
    \<open>i \<le> safe F I i n c\<close>
    using Suc.prems(1) safe_step_SucD
    by fastforce
  note safe_ih = Suc.hyps[OF safe_n_c]

  note step = safe_suc_then_step[OF predicate1D[OF Suc.prems]]

  show ?case
    using Suc.prems(1-2)
    apply -
    apply (rule safe.safeI)
      (* subgoal: skip *)
      apply blast
      (* subgoal: stateset *)
     apply blast
      (* subgoal: framed opstep *)
    apply (simp add: le_fun_def del: split_paired_All)
    apply (elim disjE conjE exE)
      (** exit *)
     apply force
      (** continue *)
    apply clarsimp
    apply (drule(2) step)
    apply clarsimp
    apply (intro exI conjI)
      apply assumption
     apply assumption
    apply (rule safe_seq, blast)
    apply (blast dest: safe_ih)
    done
qed force


subsubsection \<open> Safety of internal nondeterminism \<close>

lemma safe_indet:
  \<open>safe F I q n ca s \<Longrightarrow> safe F I q n cb s \<Longrightarrow> safe F I q n (ca \<^bold>\<sqinter> cb) s\<close>
proof (induct n arbitrary: ca cb s)
  case (Suc n)
  show ?case
    using Suc.prems
    apply -
    apply (rule safeI)
      (* subgoal: rely *)
      apply fast
      (* subgoal: state inv *)
     apply fast
      (* subgoal: framed opstep *)
    apply (clarsimp simp add: conj_disj_distribL[symmetric] simp del: sup_apply)
    apply (meson Suc_n_not_le_n order.refl inf_sup_ord(3,4) linorder_le_cases safe_mono; fail)
    done
qed blast


subsubsection \<open> Safety of external nondeterminism \<close>

lemma safe_endet:
  \<open>safe F I q n ca s \<Longrightarrow> safe F I q n cb s \<Longrightarrow> safe F I q n (ca \<^bold>\<box> cb) s\<close>
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
      (* subgoal: local frame opstep *)
    apply (clarsimp simp del: sup_apply)
    apply (simp only: disj.assoc[symmetric, of _ _ \<open>_ \<or> _\<close>])
    apply (erule disjE, erule disjE)
      apply (clarsimp simp add: conj_disj_distribR_middle[symmetric] conj_disj_distribL[symmetric])
      apply (meson inf_sup_ord(4) lessI order_le_less safe_mono sup.cobounded1; fail)
     apply (elim disjE; clarify)
      apply (metis Suc.hyps safe_step_SucD safe_suc_then_step)
     apply (metis Suc.hyps safe_step_SucD safe_suc_then_step)
    apply blast
    done
qed blast


subsection \<open> Safety of parallel \<close>

lemma safe_parallel:
  \<open>safe (Ib \<^emph> F) Ia qa n ca sa \<Longrightarrow>
    safe (Ia \<^emph> F) Ib qb n cb sb \<Longrightarrow>
    \<^bold>J sa sb sc \<Longrightarrow>
    safe F (Ia \<^emph> Ib) (qa \<^emph> qb) n (ca \<parallel> cb) sc\<close>
proof (induct n arbitrary: ca cb sa sb sc)
  case (Suc n)

  note safe_step1 = safe_suc_then_step[OF Suc.prems(1)]
  note safe_step2 = safe_suc_then_step[OF Suc.prems(2)]

  show ?case
  proof (rule safeI; fast?; (intro conjI)?; (simp only: fst_conv snd_conv)?)
    show \<open>(Ia \<^emph> Ib) sc\<close>
      using Suc.prems
      by (metis safe_then_state_inv sepconj_apply)
  next
    fix m f scf \<alpha> scf' c'
    assume assms2:
      \<open>Suc n = Suc m\<close>
      \<open>F f\<close>
      \<open>\<^bold>J sc f scf\<close>
      \<open>opstep \<alpha> (scf, ca \<parallel> cb) (scf', c')\<close>

    obtain saf where saf_defn:
      \<open>\<^bold>J sa f saf\<close>
      \<open>\<^bold>J saf sb scf\<close>
      using Suc.prems assms2 join_assoc2
      by blast

    obtain sbf where sbf_defn:
      \<open>\<^bold>J sb f sbf\<close>
      \<open>\<^bold>J sbf sa scf\<close>
      using Suc.prems assms2 join_assoc2 join_comm
      by blast

    note state_invs = Suc.prems(1-2)[THEN safe_then_state_inv]
    then have framed_invs:
      \<open>(Ia \<^emph> F) saf\<close>
      \<open>(Ib \<^emph> F) sbf\<close>
      using assms2 saf_defn sbf_defn
      by (metis sepconjI)+

    show \<open>\<exists>s'. \<^bold>J s' f scf' \<and> (\<alpha> = Tau \<longrightarrow> s' = sc) \<and> safe F (Ia \<^emph> Ib) (qa \<^emph> qb) m c' s'\<close>
      using assms2 Suc.prems(3) framed_invs
      apply (simp add: del: sup_apply)
      apply (elim disjE conjE exE)
        (* subgoal: done *)
        apply (metis Suc.prems(1,2) safe_skip_iff sepconjI)
        (* subgoal: left *)
       apply (cut_tac sbf_defn)
       apply (frule safe_step1, fast intro: join_comm, fast)
       apply clarsimp
       apply (frule(1) join_assoc3[of sb _ _ _ scf'])
       apply clarsimp
       apply (metis (no_types, lifting) Suc.hyps Suc.prems(2) fst_conv join_comm
          opstep_tau_preserves_heap safe_step_SucD)
        (* subgoal right *)
       apply (cut_tac saf_defn)
       apply (frule safe_step2, fast intro: join_comm, fast)
       apply clarsimp
       apply (frule(1) join_assoc3[of sa _ _ _ scf'])
      apply clarsimp
      apply (metis (no_types, opaque_lifting) Suc.hyps Suc.prems(1) eq_fst_iff opstep_tau_preserves_heap
          safe_step_SucD)
      done
  qed
qed (blast intro: sepconjI)


subsection \<open> Safety of conj \<close>

lemma safe_Conj:
  assumes niassms:
    \<open>F \<le> cancellative (\<Squnion>\<I>)\<close>
    \<open>\<I> \<noteq> {}\<close>
    \<open>Q \<noteq> {}\<close>
    and iassms:
    \<open>\<forall>I\<in>\<I>. \<forall>q\<in>Q. safe F I q n c s\<close>
  shows
    \<open>safe F (\<Sqinter>\<I>) (\<Sqinter>Q) n c s\<close>
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
      (* framed opstep *)
    apply (clarsimp simp del: inf_apply Inf_apply)
      (** find \<^emph>\<open>some\<close> execution, to get the splitting for the existential *)
    apply (subgoal_tac \<open>(\<exists>Ia. Ia \<in> \<I>) \<and> (\<exists>qa. qa \<in> Q)\<close>)
     prefer 2
     apply blast
    apply clarsimp
    apply (frule bspec[of \<I>], assumption, drule bspec[of Q], assumption)
    apply (drule(3) safe_suc_then_step)
    apply clarsimp
    apply (rename_tac sx')
    apply (rule_tac x=sx' in exI)
    apply (intro conjI)
      apply fast
     apply fast
    apply (rule Suc.hyps)
      (** pin down the actual execution *)
    apply clarsimp
    apply (frule_tac x=I in bspec, assumption, drule_tac x=q in bspec, assumption)
    apply (drule(3) safe_suc_then_step)
    apply clarsimp
    apply (rename_tac sy')
      (*** they're the same thing, by cancellativity *)
    apply (drule_tac c=\<open>cancellative (I \<squnion> Ia)\<close> in order.trans)
     apply (metis Sup1_I cancellative_antimono predicate1I sup1E)
    apply (subgoal_tac \<open>sx' = sy'\<close>)
     prefer 2
     apply (metis cancellativeD inf_sup_ord(4) predicate1D safe_then_state_inv sup_ge1)
    apply fast
    done
qed


section \<open> Semantic Proof \<close>

definition semsat (\<open>_, _ \<Turnstile> { _ } _ { _ }\<close> [50,0,0,50,0] 50) where
  \<open>F, I \<Turnstile> { p } c { q } \<equiv> \<forall>n. p \<le> safe F I q n c\<close>

lemma semsat_weaken:
  \<open>F, I \<Turnstile> { p } c { q } \<Longrightarrow>
    F' \<le> F \<Longrightarrow>
    I \<le> I' \<Longrightarrow>
    p' \<le> p \<Longrightarrow>
    q \<le> q' \<Longrightarrow>
    F', I' \<Turnstile> { p' } c { q' }\<close>
  unfolding semsat_def
  apply clarsimp
  apply (rule safe_mono[OF _ _ _ order.refl]; assumption?)
  apply blast
  done

lemmas semsat_weaken_state_inv =
  semsat_weaken[OF _ order.refl _ order.refl order.refl]

lemmas semsat_weaken_frame_inv =
  semsat_weaken[OF _ _ order.refl order.refl order.refl]

lemmas semsat_weaken_prepost =
  semsat_weaken[OF _ order.refl order.refl]

lemmas semsat_weaken_precond =
  semsat_weaken[OF _ order.refl order.refl _ order.refl]

lemmas semsat_weaken_postcond =
  semsat_weaken[OF _ order.refl order.refl order.refl]

lemma semsat_skip:
  \<open>p \<le> q \<Longrightarrow> p \<le> I \<Longrightarrow> F, I \<Turnstile> { p } Skip { q }\<close>
  unfolding semsat_def
  by (simp add: le_fun_def)

lemma semsat_frame:
  \<open>F \<^emph> F', I \<Turnstile> { p } c { q } \<Longrightarrow> F, I \<^emph> F' \<Turnstile> { p \<^emph> F' } c { q \<^emph> F' }\<close>
  using safe_frame
  by (clarsimp simp add: semsat_def le_fun_def sepconj_apply, blast)

lemma semsat_atom:
  \<open>\<forall>f\<le>F. sp ar (p \<^emph> f) \<le> q \<^emph> f \<Longrightarrow>
    p \<le> I \<Longrightarrow>
    q \<le> I \<Longrightarrow>
    F, I \<Turnstile> { p } \<langle>ar\<rangle> { q }\<close>
  apply (clarsimp simp add: semsat_def)
  apply (frule_tac n=n in safe_atom, fast)
  apply (meson le_sup_iff safe_mono_invD)
  done

lemma semsat_seq:
  \<open>F, I \<Turnstile> { p } ca { px } \<Longrightarrow>
    F, I \<Turnstile> { px } cb { q } \<Longrightarrow>
    F, I \<Turnstile> { p } (ca ;; cb) { q }\<close>
  apply (clarsimp simp add: semsat_def le_fun_def)
  apply (rule safe_seq, fast+)
  done

lemma semsat_iter:
  \<open>F, I \<Turnstile> { i } c { i } \<Longrightarrow>
    F, I \<Turnstile> { i } Iter c { i }\<close>
  unfolding semsat_def
  apply (clarsimp simp add: le_fun_def)
  apply (rule safe_iter[where i=i]; force)
  done

lemma semsat_indet:
  \<open>F, I \<Turnstile> { p } ca { qa } \<Longrightarrow>
    F, I \<Turnstile> { p } cb { qb } \<Longrightarrow>
    F, I \<Turnstile> { p } ca \<^bold>\<sqinter> cb { qa \<squnion> qb }\<close>
  apply (clarsimp simp add: semsat_def le_fun_def)
  apply (rule safe_indet[where I=I and q=\<open>qa \<squnion> qb\<close>])
   apply (meson safe_mono_postD sup.cobounded1  sup.cobounded2)+
  done

lemma semsat_endet:
  \<open>F, I \<Turnstile> { p } ca { qa } \<Longrightarrow>
    F, I \<Turnstile> { p } cb { qb } \<Longrightarrow>
    F, I \<Turnstile> { p } ca \<^bold>\<box> cb { qa \<squnion> qb }\<close>
  apply (clarsimp simp add: semsat_def le_fun_def)
  apply (rule safe_endet[where I=I and q=\<open>qa \<squnion> qb\<close>])
   apply (meson safe_mono_postD sup.cobounded1  sup.cobounded2)+
  done

lemma semsat_par:
  \<open>Ib \<^emph> F, Ia \<Turnstile> { pa } ca { qa } \<Longrightarrow>
   Ia \<^emph> F, Ib \<Turnstile> { pb } cb { qb } \<Longrightarrow>
   F, Ia \<^emph> Ib \<Turnstile> { pa \<^emph> pb } ca \<parallel> cb { qa \<^emph> qb }\<close>
  apply (clarsimp simp add: semsat_def le_fun_def sepconj_apply)
  apply (rule safe_parallel; fast)
  done

lemma semsat_Conj:
  assumes
    \<open>F \<le> cancellative (\<Squnion>\<I>)\<close>
    \<open>\<I> \<noteq> {}\<close>
    \<open>Q \<noteq> {}\<close>
    \<open>\<forall>I\<in>\<I>. \<forall>q\<in>Q. F, I \<Turnstile> { p } c { q }\<close>
  shows
    \<open>F, \<Sqinter>\<I> \<Turnstile> { p } c { \<Sqinter>Q }\<close>
  using assms
  apply (clarsimp simp add: semsat_def)
  apply (rule safe_Conj; fast)
  done

lemma semsat_Disj:
  assumes \<open>\<forall>p\<in>P. F, I \<Turnstile> { p } c { q }\<close>
  shows \<open>F, I \<Turnstile> { \<Squnion>P } c { q }\<close>
  using assms
  by (force simp add: semsat_def)


end