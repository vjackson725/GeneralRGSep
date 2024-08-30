theory Soundness2
  imports "../Semantics"
begin

inductive ptrace ::
  \<open>('l::pre_perm_alg \<times> 's::pre_perm_alg) comm \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's) list \<Rightarrow>
    bool\<close>
  where
  ptrace_nil[intro!]: \<open>ptrace c r g q F []\<close>
| ptrace_postcond1[intro]:
  \<open>q (hl, hs) \<Longrightarrow> ptrace Skip r g q F [(hl,hs)]\<close>
| ptrace_postcond2[intro]:
  \<open>ptrace Skip r g q F tt \<Longrightarrow>
    q (hl, hs) \<Longrightarrow> ptrace Skip r g q F ((hl,hs) # tt)\<close>
| ptrace_rely[intro]:
  \<open>ptrace c r g q F ((hl,hs') # tt) \<Longrightarrow>
    r hs hs' \<Longrightarrow>
    ptrace c r g q F ((hl,hs) # (hl,hs') # tt)\<close>
| ptrace_opstep[intro]:
  \<open>ptrace c' r g q F ((hl',hs') # tt) \<Longrightarrow>
    ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<Longrightarrow>
    (a \<noteq> Tau \<longrightarrow> g hs hs') \<Longrightarrow>
    ptrace c r g q F ((hl,hs) # (hl',hs') # tt)\<close>
| ptrace_opstep_frame[intro]:
  \<open>ptrace c' r g q F ((hl',hs') # tt) \<Longrightarrow>
    F hlf \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    hl' ## hlf \<Longrightarrow>
    ((hl + hlf, hs), c) \<midarrow>a\<rightarrow> ((hl' + hlf, hs'), c') \<Longrightarrow>
    (a = Tau \<longrightarrow> hl' = hl) \<Longrightarrow>
    (a \<noteq> Tau \<longrightarrow> g hs hs') \<Longrightarrow>
    ptrace c r g q F ((hl,hs) # (hl',hs') # tt)\<close>

inductive_cases ptrace_nilE[elim!]: \<open>ptrace c r g q F []\<close>
inductive_cases ptrace_singletonE[elim!]: \<open>ptrace c r g q F [s]\<close>
inductive_cases ptrace_stepE[elim]: \<open>ptrace c r g q F (s # s' # tt)\<close>

subsubsection \<open> Monotonicity of ptrace \<close>

lemma ptrace_postpred_monoD:
  \<open>ptrace c r g q F tt \<Longrightarrow> q \<le> q' \<Longrightarrow> ptrace c r g q' F tt\<close>
  by (induct rule: ptrace.induct) blast+

lemmas ptrace_postpred_mono = ptrace_postpred_monoD[rotated]

lemma ptrace_guarantee_monoD:
  \<open>ptrace c r g q F tt \<Longrightarrow> g \<le> g' \<Longrightarrow> ptrace c r g' q F tt\<close>
  by (induct rule: ptrace.induct) blast+

lemmas ptrace_guarantee_mono = ptrace_guarantee_monoD[rotated]

lemma ptrace_rely_monoD:
  \<open>ptrace c r g q F tt \<Longrightarrow> r \<le> r' \<Longrightarrow> ptrace c r' g q F tt\<close>
  by (induct rule: ptrace.induct) blast+

lemmas ptrace_rely_mono = ptrace_rely_monoD[rotated]

lemma ptrace_drop_stepsD:
  \<open>ptrace c r g q F tt \<Longrightarrow> ptrace c r g q F (drop n tt)\<close>
  apply (induct arbitrary: n rule: ptrace.inducts)
       apply force
      apply (force simp add: drop_Cons' ptrace_nil ptrace_postcond1)
     apply (force simp add: drop_Cons')
    apply (fastforce simp add: drop_Cons' if_distrib if_bool_eq_conj)
   apply (simp add: drop_Cons' if_distrib if_bool_eq_conj)
   apply (intro conjI impI)
     apply fastforce
  oops

lemma ptrace_frameset_monoD:
  \<open>ptrace c r g q F tt \<Longrightarrow> F \<le> F' \<Longrightarrow> ptrace c r g q F' tt\<close>
  by (induct rule: ptrace.inducts) blast+


inductive rgtrace :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('l \<times> 's) list \<Rightarrow> bool\<close> where
  rgtrace_nil: \<open>rgtrace r g []\<close>
| rgtrace_start: \<open>rgtrace r g [s]\<close>
| rgtrace_step:
  \<open>rgtrace r g (s1 # tt) \<Longrightarrow>
    r (snd s1) (snd s2) \<or> g (snd s1) (snd s2) \<Longrightarrow>
    rgtrace r g (s2 # s1 # tt)\<close>

abbreviation \<open>rgtraces r g \<equiv> Collect (rgtrace r g)\<close>

abbreviation \<open>ptraces c r g q F \<equiv> Collect (ptrace c r g q F)\<close>


section \<open> safe \<close>

definition
  \<open>safe c r g q F s n \<equiv> rgtraces r g \<inter> ptraces c r g q F \<noteq> {}\<close>

lemma safe_postpred_monoD:
  \<open>q \<le> q' \<Longrightarrow> safe c r g q F s n \<Longrightarrow> safe c r g q' F s n\<close>
  sorry

lemmas safe_postpred_mono = safe_postpred_monoD[rotated]

lemma safe_guarantee_monoD:
  \<open>g \<le> g' \<Longrightarrow> safe c r g q F s n \<Longrightarrow> safe c r g' q F s n\<close>
  sorry

lemmas safe_guarantee_mono = safe_guarantee_monoD[rotated]

lemma safe_rely_antimonoD:
  \<open>r' \<le> r \<Longrightarrow> safe c r g q F s n \<Longrightarrow> safe c r' g q F s n\<close>
  sorry

lemmas safe_rely_mono = safe_rely_monoD[rotated]

lemma safe_drop_stepsD:
  \<open>safe c r g q F s n \<Longrightarrow> m \<le> n \<Longrightarrow> safe c r g q F s m\<close>
  sorry

lemma safe_frameset_monoD:
  \<open>safe c r g q F s n \<Longrightarrow> F \<le> F' \<Longrightarrow> safe c r g q F' s n\<close>
  sorry


subsection \<open> Safety of Skip \<close>

lemma ptrace_skip':
  \<open>sswa r q s \<Longrightarrow> safe Skip r g (sswa r q) F s n\<close>
  unfolding safe_def
  apply (induct n arbitrary: s q)
   apply force
  apply clarsimp
  apply (case_tac n, blast)
  apply (metis length_Cons ptrace_postcond2)
  done

lemma ptrace_skip:
  \<open>p s \<Longrightarrow> sswa r p \<le> q \<Longrightarrow> safe Skip r g q F s n\<close>
  by (simp add: ptrace_skip' safe_postpred_monoD sswa_trivial)


subsection \<open> Safety of frame \<close>

lemma ptrace_frame':
  \<open>ptrace c hl hs r g q F \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    (sswa (r \<squnion> g) f) \<le> F \<times>\<^sub>P \<top> \<Longrightarrow>
    sswa (r \<squnion> g) f (hlf, hs) \<Longrightarrow>
    ptrace c (hl + hlf) hs r g (q \<^emph>\<and> sswa (r \<squnion> g) f) (F \<midarrow>\<^emph> F)\<close>
proof (induct arbitrary: hlf rule: safe.induct)
  case (ptrace_nil c hl hs r g q F)
  then show ?case by blast
next
  case (ptrace_suc c q hl hs r n g F)
  show ?case
    using ptrace_suc.prems
    apply -
    apply (rule safe.ptrace_suc)
      (* subgoal: skip *)
        apply (clarsimp simp add: sepconj_conj_def simp del: sup_apply)
        apply (drule mp[OF ptrace_suc.hyps(1)])
        apply blast
      (* subgoal: rely step *)
       apply (rule ptrace_suc.hyps(3), blast, blast, blast)
       apply (rule sswa_step, rule sup2I1, blast, blast)
      (* subgoal: plain opstep *)
     apply (frule(1) ptrace_suc.hyps(5))
      apply (force simp add: le_fun_def)
     apply (clarsimp simp del: sup_apply top_apply)
     apply (erule opstep_act_cases)
      apply force
     apply (metis sswa_stepD sup2I2)
      (* subgoal: local framed opstep *)
    apply (clarsimp simp add: partial_add_assoc2[of hl hlf] simp del: sup_apply top_apply)
    apply (rename_tac c hlf2 st')
    apply (frule ptrace_suc.hyps(5)[rotated 1])
      apply (metis (full_types) disjoint_add_leftL disjoint_add_leftR disjoint_add_left_commute2
        partial_add_commute pred_Times_iff rev_predicate1D sepimp_def)
     apply (metis disjoint_add_swap_lr)
    apply (clarsimp simp del: sup_apply top_apply)
    apply (rule_tac x=\<open>hl' + hlf\<close> in exI, rule conjI)
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

lemma ptrace_frame:
  \<open>ptrace c hl hs r g q F \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    f (hlf, hs) \<Longrightarrow>
    sswa (r \<squnion> g) f \<le> F \<times>\<^sub>P \<top> \<Longrightarrow>
    sswa (r \<squnion> g) f \<le> f' \<Longrightarrow>
    F' \<le> F \<midarrow>\<^emph> F \<Longrightarrow>
    ptrace c (hl + hlf) hs r g (q \<^emph>\<and> f') F'\<close>
  apply (rule ptrace_postpred_monoD)
   apply (rule ptrace_frameset_antimonoD)
    apply (rule ptrace_frame'[where f=f]; blast)
   apply blast
  apply (blast dest: sepconj_conj_monoR)
  done


subsection \<open> Safety of Atomic \<close>

lemma ptrace_atom':
  \<open>sp b (wssa  r p) \<le> sswa r q \<Longrightarrow>
    \<forall>f. f \<le> F \<longrightarrow> sp b (wssa r (p \<^emph>\<and> \<L> f)) \<le> sswa r (q \<^emph>\<and> \<L> f) \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    wssa  r p (hl, hs) \<Longrightarrow>
    ptrace (Atomic b) hl hs r g (sswa r q) F\<close>
proof (induct n arbitrary: hl hs)
  case 0
  then show ?case by force
next
  case (Suc n)
  show ?case
    using Suc.prems
    apply (intro safe.ptrace_suc)
      (* subgoal: skip *)
          apply force
      (* subgoal: rely *)
       apply (rule Suc.hyps; force simp add: wssa_step)
      (* subgoal: plain opstep *)
     apply (simp add: opstep_iff del: top_apply sup_apply)
     apply (metis predicate2D rel_Times_iff ptrace_skip' sp_impliesD)
      (* subgoal: local framed opstep *)
    apply (clarsimp simp add: opstep_iff sp_def[of b] imp_ex_conjL le_fun_def simp del: sup_apply)
    apply (drule_tac x=\<open>(=) hlf\<close> in spec)
    apply (drule mp, force)
    apply (drule spec2, drule spec2, drule mp, fast, drule mp,
        rule predicate1D[OF wlp_rely_sepconj_conj_semidistrib])
     apply (rule sepconj_conjI, blast; force simp add: wlp_def)
    apply (drule predicate1D[OF sp_rely_sepconj_conj_semidistrib])
    apply (clarsimp simp add: sepconj_conj_def)
    apply (metis (mono_tags, lifting) prod.collapse rel_Times_iff ptrace_skip' sp_def)
    done
qed

lemma ptrace_atom:
  \<open>sp b (wssa r p) \<le> sswa r q \<Longrightarrow>
    \<forall>f. f \<le> F \<longrightarrow> sp b (wssa r (p \<^emph>\<and> \<L> f)) \<le> sswa r (q \<^emph>\<and> \<L> f) \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    wssa r p (hl, hs) \<Longrightarrow>
    sswa r q \<le> q' \<Longrightarrow>
    ptrace (Atomic b) hl hs r g q' F\<close>
  by (meson ptrace_postpred_mono ptrace_atom')


subsection \<open> Safety of Sequencing \<close>

lemma ptrace_seq_assoc_left:
  \<open>ptrace c hl hs r g q F \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    ptrace ((c1 ;; c2) ;; c3) hl hs r g q F\<close>
  apply (induct arbitrary: c1 c2 c3 rule: ptrace.inducts)
   apply force
  apply (rule ptrace_suc)
     apply blast
    apply blast
   apply (clarsimp simp add: opstep_iff, metis)+
  done

lemma ptrace_seq_assoc_right:
  \<open>ptrace c hl hs r g q F \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    ptrace (c1 ;; c2 ;; c3) hl hs r g q F\<close>
  apply (induct arbitrary: c1 c2 c3 rule: ptrace.inducts)
   apply force
  apply (rule ptrace_suc)
     apply blast
    apply blast
   apply (clarsimp simp add: opstep_iff, metis)+
  done

lemma ptrace_seq':
  \<open>ptrace c1 hl hs r g q F \<Longrightarrow>
    (\<forall>m\<le>n. \<forall>hl' hs'. q (hl', hs') \<longrightarrow> safe m c2 hl' hs' r g q' F) \<Longrightarrow>
    ptrace (c1 ;; c2) hl hs r g q' F\<close>
proof (induct arbitrary: c2 q' rule: ptrace.inducts)
  case (ptrace_suc c q hl hs r n g F)

  have ptrace_c2:
    \<open>\<And>m hl' hs'. m \<le> n \<Longrightarrow> q (hl', hs') \<Longrightarrow> safe m c2 hl' hs' r g q' F\<close>
    \<open>\<And>hl' hs'. q (hl', hs') \<Longrightarrow> safe (Suc n) c2 hl' hs' r g q' F\<close>
    using ptrace_suc.prems
    by force+
  then show ?case
    using ptrace_suc.prems(1) ptrace_suc.hyps(1)
    apply -
    apply (rule safe.ptrace_suc)
       apply force
      (* subgoal: rely *)
      apply (simp add: ptrace_suc.hyps(3); fail)
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: opstep_iff simp del: sup_apply)
     apply (elim disjE conjE exE)
      apply clarsimp
     apply (frule ptrace_suc.hyps(4))
     apply (metis act.distinct(1) ptrace_c2(1))
      (* subgoal: local framed opstep *)
    apply (clarsimp simp add: opstep_iff simp del: sup_apply)
    apply (erule disjE, force)
    apply (clarsimp simp del: sup_apply)
    apply (frule(2) ptrace_suc.hyps(5))
    apply (metis act.distinct(1) ptrace_c2(1))
    done
qed force


lemma ptrace_seq:
  \<open>ptrace c1 hl hs r g q F \<Longrightarrow>
    (\<forall>hl' hs'. q (hl', hs') \<longrightarrow> ptrace c2 hl' hs' r g q' F) \<Longrightarrow>
    ptrace (c1 ;; c2) hl hs r g q' F\<close>
  by (force intro: ptrace_seq' ptrace_step_monoD)


subsection \<open> Safety of Iter \<close>

lemma ptrace_iter:
  \<open>(\<And>hl' hs'. sswa r i (hl', hs') \<Longrightarrow> ptrace c hl' hs' r g (sswa r i) F) \<Longrightarrow>
    sswa r i (hl, hs) \<Longrightarrow>
    ptrace (Iter c) hl hs r g (sswa r i) F\<close>
proof (induct n arbitrary: i hl hs)
  case (Suc n)

  have ptrace_ih:
    \<open>\<And>m hl' hs'. m \<le> n \<Longrightarrow> sswa r i (hl', hs') \<Longrightarrow> safe m c hl' hs' r g (sswa r i) F\<close>
    \<open>\<And>hl' hs'. sswa r i (hl', hs') \<Longrightarrow> safe (Suc n) c hl' hs' r g (sswa r i) F\<close>
    using Suc.prems(1)
    by (force intro: ptrace_step_monoD)+

  note ptrace_suc_c = ptrace_sucD[OF ptrace_ih(2)]

  show ?case
    using Suc.prems(2)
    apply -
    apply (rule safe.ptrace_suc)
      (* subgoal: skip *)
       apply blast
      (* subgoal: rely *)
      apply (rule Suc.hyps)
       apply (simp add: ptrace_ih(1); fail)
      apply (metis sswa_step)
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: le_Suc_eq all_conj_distrib opstep_iff)
     apply (erule disjE)
      apply (simp add: rely_rel_wlp_impl_sp ptrace_skip'; fail)
     apply clarsimp
     apply (rule ptrace_seq')
      apply (rule ptrace_ih(1))
       apply blast
      apply (simp add: rely_rel_wlp_impl_sp; fail)
     apply clarsimp
     apply (rule ptrace_step_monoD[rotated], assumption)
     apply (simp add: Suc.hyps ptrace_ih(1); fail)
      (* subgoal: locally framed opstep *)
    apply (clarsimp simp add: le_Suc_eq all_conj_distrib opstep_iff simp del: sup_apply)
    apply (erule disjE)
     apply (simp add: rely_rel_wlp_impl_sp ptrace_skip'; fail)
    apply clarsimp
    apply (rule ptrace_seq')
     apply (rule ptrace_ih(1))
      apply blast
     apply (simp add: rely_rel_wlp_impl_sp; fail)
    apply clarsimp
    apply (rule ptrace_step_monoD[rotated], assumption)
    apply (simp add: Suc.hyps ptrace_ih(1); fail)
    done
qed force


subsubsection \<open> Safety of internal nondeterminism \<close>

lemma ptrace_indet:
    \<open>ptrace c1 hl hs r g q F \<Longrightarrow>
      ptrace c2 hl hs r g q F \<Longrightarrow>
      ptrace (c1 \<^bold>+ c2) hl hs r g q F\<close>
proof (induct n arbitrary: c1 c2 hl hs)
  case 0
  then show ?case by blast
next
  case (Suc n)

  have safeSuc:
    \<open>safe (Suc n) c1 hl hs r g q F\<close>
    \<open>safe (Suc n) c2 hl hs r g q F\<close>
    using Suc.prems
    by simp+
  note ptrace_suc1 = ptrace_sucD[OF safeSuc(1)]
  note ptrace_suc2 = ptrace_sucD[OF safeSuc(2)]

  have
    \<open>\<forall>m\<le>n. safe m c1 hl hs r g q F\<close>
    \<open>\<forall>m\<le>n. safe m c2 hl hs r g q F\<close>
    using Suc.prems
    by (meson le_SucI ptrace_step_monoD)+
  then show ?case
    apply -
    apply (rule ptrace_suc)
       apply blast
      (* subgoal: rely *)
      apply (metis Suc.hyps ptrace_suc1(2) ptrace_suc2(2))
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: opstep_iff simp del: sup_apply)
     apply (elim disjE conjE exE)
      apply (force dest: ptrace_suc1(3-4))
     apply (force dest: ptrace_suc2(3-4))
      (* subgoal: local frame opstep *)
    apply (clarsimp simp add: opstep_iff simp del: sup_apply)
    apply (elim disjE conjE exE)
     apply (simp add: ptrace_suc1(5-6))
    apply (simp add: ptrace_suc2(5-6))
    done
qed


subsubsection \<open> Safety of external nondeterminism \<close>

lemma ptrace_endet:
    \<open>ptrace c1 hl hs r g q F \<Longrightarrow>
      ptrace c2 hl hs r g q F \<Longrightarrow>
      ptrace (c1 \<box> c2) hl hs r g q F\<close>
proof (induct n arbitrary: c1 c2 hl hs)
  case 0
  then show ?case by blast
next
  case (Suc n)

  have safeSuc:
    \<open>safe (Suc n) c1 hl hs r g q F\<close>
    \<open>safe (Suc n) c2 hl hs r g q F\<close>
    using Suc.prems
    by simp+
  note ptrace_suc1 = ptrace_sucD[OF safeSuc(1)]
  note ptrace_suc2 = ptrace_sucD[OF safeSuc(2)]

  have
    \<open>\<forall>m\<le>n. safe m c1 hl hs r g q F\<close>
    \<open>\<forall>m\<le>n. safe m c2 hl hs r g q F\<close>
    using Suc.prems
    by (meson le_SucI ptrace_step_monoD)+
  then show ?case
    apply -
    apply (rule ptrace_suc)
       apply blast
      (* subgoal: rely *)
      apply (metis Suc.hyps ptrace_suc1(2) ptrace_suc2(2))
      (* subgoal: plain opstep *)
     apply (clarsimp simp add: opstep_iff simp del: sup_apply)
     apply (elim disjE conjE exE)
          apply (force dest: ptrace_suc1(3-4))
         apply (force dest: ptrace_suc2(3-4))
        apply (frule opstep_tau_preserves_heap, clarsimp)
        apply (simp add: Suc.hyps ptrace_suc1(3); fail)
       apply (frule opstep_tau_preserves_heap, clarsimp)
       apply (simp add: Suc.hyps ptrace_suc2(3); fail)
      apply blast
     apply blast
      (* subgoal: local frame opstep *)
    apply (clarsimp simp add: opstep_iff simp del: sup_apply)
    apply (elim disjE conjE exE)
         apply (metis act.distinct(1) ptrace_suc1(5-6))
        apply (metis act.distinct(1) ptrace_suc2(5-6))
      (* subsubgoal: left tau passthrough *)
       apply (frule ptrace_suc1(5), blast)
        apply clarsimp
       apply (frule opstep_tau_preserves_heap)
       apply (clarsimp simp del: sup_apply)
       apply (metis Suc.hyps order.refl)
      (* subsubgoal: right tau passthrough *)
      apply (frule ptrace_suc2(5), blast)
       apply clarsimp
      apply (frule opstep_tau_preserves_heap)
      apply (clarsimp simp del: sup_apply)
      apply (metis Suc.hyps order.refl)
      (* subsubgoal: right skip tau *)
     apply blast
      (* subsubgoal: left skip tau *)
    apply blast
    done
qed


subsection \<open> Safety of parallel \<close>

(* TODO: weaken the frame sets *)
lemma ptrace_parallel':
  \<open>ptrace c1 hl1 hs (r \<squnion> g2) g1 (sswa (r \<squnion> g2) q1) \<top> \<Longrightarrow>
    ptrace c2 hl2 hs (r \<squnion> g1) g2 (sswa (r \<squnion> g1) q2) \<top> \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    ptrace (c1 \<parallel> c2) (hl1 + hl2) hs r (g1 \<squnion> g2)
      ((sswa (r \<squnion> g2) q1) \<^emph>\<and> (sswa (r \<squnion> g1) q2)) \<top>\<close>
proof (induct n arbitrary: c1 c2 hl1 hl2 hs)
  case 0
  then show ?case by force
next
  case (Suc n)

  note ptrace_suc1 = ptrace_sucD[OF Suc.prems(1)]
  note ptrace_suc2 = ptrace_sucD[OF Suc.prems(2)]

  have
    \<open>\<forall>m\<le>n. safe m c1 hl1 hs (r \<squnion> g2) g1 (sswa (r \<squnion> g2) q1) \<top>\<close>
    \<open>\<forall>m\<le>n. safe m c2 hl2 hs (r \<squnion> g1) g2 (sswa (r \<squnion> g1) q2) \<top>\<close>
     apply (metis Suc.prems(1) le_Suc_eq ptrace_step_monoD)
    apply (metis Suc.prems(2) le_Suc_eq ptrace_step_monoD)
    done
  then show ?case
    using Suc.prems(3-)
    apply -
    apply (rule ptrace_suc)
        apply blast
       apply (metis Suc.hyps ptrace_suc1(2) ptrace_suc2(2) sup2CI)
    subgoal
      apply (simp add: opstep_iff del: sup_apply top_apply)
      apply (elim disjE conjE exE)
        (* subgoal: tau *)
        apply (clarsimp simp del: sup_apply top_apply)
        apply (insert ptrace_suc1(1) ptrace_suc2(1))
        apply (clarsimp simp del: sup_apply top_apply)
        apply (rule ptrace_skip[of \<open>sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2\<close>])
         apply (clarsimp simp add: sepconj_conj_def[of \<open>sp _ _\<close>] simp del: sup_apply top_apply)
         apply blast
        apply (rule sp_rely_sepconj_conj_semidistrib_mono)
         apply (clarsimp simp add: sp_comp_rel simp del: sup_apply top_apply; fail)
        apply (clarsimp simp add: sp_comp_rel simp del: sup_apply top_apply; fail)
        (* subgoal: left *)
       apply (frule ptrace_suc1(5)[rotated], force, force)
       apply (erule opstep_act_cases)
        apply (clarsimp simp del: sup_apply top_apply)
        apply (rule Suc.hyps; blast)
       apply (frule ptrace_suc1(6)[rotated], force, blast, blast)
       apply (clarsimp simp del: sup_apply top_apply)
       apply (metis Suc.hyps ptrace_suc2(2) sup2CI)
        (* subgoal: right *)
      apply (clarsimp simp add: partial_add_commute[of hl1] simp del: sup_apply top_apply)
      apply (frule ptrace_suc2(5)[rotated], blast, metis disjoint_sym)
      apply (clarsimp simp add: partial_add_commute[symmetric, of hl1] disjoint_sym_iff
          simp del: sup_apply top_apply)
      apply (erule opstep_act_cases)
       apply (clarsimp simp del: sup_apply top_apply)
       apply (rule Suc.hyps; blast)
      apply (clarsimp simp add: partial_add_commute[symmetric, of hl2] disjoint_sym_iff
          simp del: sup_apply top_apply)
      apply (frule ptrace_suc2(6)[rotated], blast, blast, force intro: disjoint_sym)
      apply (clarsimp simp add: partial_add_commute[symmetric, of hl1] disjoint_sym_iff
          simp del: sup_apply top_apply)
      apply (intro conjI)
       apply (rule Suc.hyps)
         apply (rule sup2I2[THEN ptrace_suc1(2)], fast)
        apply fast
       apply (metis disjoint_sym)
      apply force
      done
    subgoal
      apply (simp add: opstep_iff del: sup_apply top_apply)
      apply (elim disjE conjE exE)
        (* subgoal: tau *)
        apply (clarsimp simp del: sup_apply top_apply)
        apply (insert ptrace_suc1(1) ptrace_suc2(1))
        apply (clarsimp simp del: sup_apply top_apply)
        apply (rule ptrace_skip[of \<open>sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2\<close>])
         apply (clarsimp simp add: sepconj_conj_def[of \<open>sp _ _\<close>] simp del: sup_apply top_apply)
         apply blast
        apply (rule sp_rely_sepconj_conj_semidistrib_mono)
         apply (simp add: sp_comp_rel; fail)
        apply (simp add: sp_comp_rel; fail)
        (* subgoal: left *)
       apply (simp add: partial_add_assoc2[of hl1] disjoint_sym_iff del: sup_apply top_apply)
       apply (frule ptrace_suc1(5)[rotated], blast, metis disjoint_add_swap_lr disjoint_sym_iff)
       apply (clarsimp simp del: sup_apply top_apply)
       apply (intro conjI)
        apply (rule_tac x=\<open>_ + _\<close> in exI)
        apply (intro conjI)
           apply (rule disjoint_add_swap_rl[rotated], fast)
           apply (metis disjoint_add_leftR disjoint_sym_iff)
          apply (metis disjoint_add_leftR disjoint_sym partial_add_assoc3)
         apply blast
        apply (erule opstep_act_cases)
         apply (metis Suc.hyps fst_conv le_disj_eq_absorb snd_conv)
        apply (clarsimp simp del: sup_apply top_apply)
        apply (frule ptrace_suc1(6)[rotated], blast, blast,
          metis disjoint_add_swap_lr disjoint_sym_iff)
        apply (rule Suc.hyps)
          apply blast
         apply (metis sup2CI ptrace_suc2(2))
        apply (metis disjoint_add_rightR partial_add_commute)
       apply (erule opstep_act_cases, blast)
       apply (clarsimp simp del: sup_apply top_apply)
       apply (frule ptrace_suc1(6)[rotated], blast, blast,
          metis disjoint_add_swap_lr disjoint_sym_iff)
       apply blast
        (* subgoal right *)
      apply (simp add: partial_add_commute[of hl1] partial_add_assoc2[of hl2] disjoint_sym_iff
          del: sup_apply top_apply)
      apply (frule ptrace_suc2(5)[rotated], blast, metis disjoint_add_swap_lr disjoint_sym_iff)
      apply (clarsimp simp del: sup_apply top_apply)
      apply (intro conjI)
       apply (rule_tac x=\<open>_ + _\<close> in exI)
       apply (intro conjI)
          apply (rule disjoint_add_swap_rl[rotated], fast)
          apply (metis disjoint_add_leftR disjoint_sym_iff)
         apply (metis disjoint_add_leftR disjoint_sym partial_add_assoc3)
        apply blast
       apply (simp add: partial_add_commute[of _ hl1] disjoint_sym_iff del: sup_apply top_apply)
       apply (subst partial_add_commute, metis disjoint_add_leftL disjoint_sym)
       apply (erule opstep_act_cases)
        apply (metis Suc.hyps fst_conv le_disj_eq_absorb snd_conv)
       apply (drule ptrace_suc2(6)[rotated], blast, blast, metis disjoint_add_right_commute2)
       apply (clarsimp simp del: sup_apply top_apply)
       apply (rule Suc.hyps)
         apply (blast intro: ptrace_suc1(2))
        apply force
       apply (metis disjoint_add_rightL disjoint_sym)
      apply (erule opstep_act_cases, force)
      apply (drule ptrace_suc2(6)[rotated], blast, blast, metis disjoint_add_swap_lr disjoint_sym)
      apply blast
      done
    done
qed

lemma ptrace_parallel:
  \<open>ptrace c1 hl1 hs (r \<squnion> g2) g1 (sswa (r \<squnion> g2) q1) \<top> \<Longrightarrow>
    ptrace c2 hl2 hs (r \<squnion> g1) g2 (sswa (r \<squnion> g1) q2) \<top> \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2 \<le> q \<Longrightarrow>
    g1 \<squnion> g2 \<le> g \<Longrightarrow>
    ptrace (c1 \<parallel> c2) (hl1 + hl2) hs r g q \<top>\<close>
  by (meson ptrace_guarantee_monoD ptrace_parallel' ptrace_postpred_mono)


subsection \<open> Safety of conj \<close>

lemma ptrace_conj':
  \<open>ptrace c hl hs r g q1 F1 \<Longrightarrow>
    ptrace c hl hs r g q2 F2 \<Longrightarrow>
    \<forall>a b c. F1 c \<longrightarrow> F2 c \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    ptrace c hl hs r g (q1 \<sqinter> q2) (F1 \<sqinter> F2)\<close>
proof (induct n arbitrary: c hl hs r g q1 q2)
  case 0
  then show ?case by blast
next
  case (Suc n)

  show ?case
    using Suc.prems
    apply -
    apply (intro ptrace_suc conjI impI allI)
         apply blast
        apply (rule Suc.hyps; blast)
      (* subgoal(s): opstep safe *)
       apply (rule Suc.hyps; blast)
      apply (blast dest: ptrace_sucD(4))
      (* subgoal(s): frame safe *)
     apply (clarsimp simp del: inf_apply)
    apply (frule ptrace_sucD(5)[where q=q1], blast, blast, blast)
    apply (frule ptrace_sucD(5)[where q=q2], blast, blast, blast)
    apply (case_tac a)
     apply (clarsimp simp del: inf_apply)
     apply (rule Suc.hyps; blast)
    apply (clarsimp simp del: inf_apply)
    apply (rename_tac hs' hl'1 hl'2)
    apply (rule exI, rule conjI, assumption, rule conjI, rule refl)
     apply (rule Suc.hyps; blast)
    apply (blast dest: ptrace_sucD(6))
    done
qed

lemma ptrace_conj:
  \<open>ptrace c hl hs r g q1 F1 \<Longrightarrow>
    ptrace c hl hs r g q2 F2 \<Longrightarrow>
    F \<le> F1 \<Longrightarrow>
    F \<le> F2 \<Longrightarrow>
    \<forall>a b c. F1 c \<longrightarrow> F2 c \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    ptrace c hl hs r g (q1 \<sqinter> q2) F\<close>
  apply (rule ptrace_frameset_antimonoD)
   apply (rule ptrace_conj', assumption, assumption, assumption)
  apply blast
  done

lemma ptrace_Conj':
  assumes frame_cancellative:
    \<open>\<forall>a b c. F c \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b\<close>
  shows
  \<open>Q \<noteq> {} \<Longrightarrow>
    \<forall>q\<in>Q. ptrace c hl hs r g q F \<Longrightarrow>
    ptrace c hl hs r g (\<Sqinter>Q) (F)\<close>
proof (induct n arbitrary: c hl hs r g Q)
  case 0
  then show ?case by blast
next
  case (Suc n)

  show ?case
    using Suc.prems
    apply -
    apply (intro ptrace_suc conjI impI allI)
         apply blast
        apply (rule Suc.hyps; blast)
      (* subgoal(s): opstep safe *)
       apply (rule Suc.hyps; blast)
      apply (blast dest: ptrace_sucD(4))
      (* subgoal(s): frame safe *)
     apply (subgoal_tac \<open>\<exists>q. q \<in> Q\<close>)
      prefer 2
      apply blast
     apply (clarsimp simp del: inf_apply Inf_apply)
     apply (frule_tac q=q in ptrace_sucD(5)[OF bspec[of _ \<open>\<lambda>q. safe _ _ _ _ _ _ q _\<close>]],
        blast, blast, blast, blast)
     apply (clarsimp simp del: inf_apply Inf_apply)
     apply (metis (no_types, lifting) Suc.hyps ptrace_sucD(5) frame_cancellative)
    apply (blast dest: ptrace_sucD(6))
    done
qed

section \<open> Soundness \<close>

lemma soundness:
  assumes \<open>rgsat c r g p q F\<close>
    and \<open>p (hl, hs)\<close>
  shows \<open>ptrace c hl hs r g q F\<close>
  using assms
proof (induct c r g p q F arbitrary: n hl hs rule: rgsat.inducts)
  case (rgsat_skip r p q g F)
  then show ?case
    by (simp add: ptrace_skip)
next
  case (rgsat_iter c r g i F p q)
  then show ?case
    using ptrace_postpred_mono[OF _ ptrace_iter[of r i n c g]]
    by blast
next
  case (rgsat_seq c1 r g p1 p2 F c2 p3)
  then show ?case
    using ptrace_seq[of n c1 hl hs r g p2 F c2 p3]
    by blast
next
  case (rgsat_indet c1 r g1 p q1 F c2 g2 q2 g q)
  then show ?case
    using ptrace_indet[of n c1 hl hs r g q F c2]
    by (meson ptrace_guarantee_mono ptrace_postpred_mono)
next
  case (rgsat_endet c1 r g1 p q1 F c2 g2 q2 g q)
  then show ?case
    using ptrace_endet[of n c1 hl hs r g q F c2]
    by (meson ptrace_guarantee_mono ptrace_postpred_mono)
next
  case (rgsat_par s1 r g2 g1 p1 q1 s2 p2 q2 g p q)
  then show ?case
    apply -
    apply (clarsimp simp add: sepconj_conj_def[of p1 p2] le_fun_def[of p]
        simp del: sup_apply top_apply)
    apply (drule spec2, drule mp, blast)
    apply (clarsimp simp del: sup_apply top_apply)
    apply (rule ptrace_parallel[where ?q1.0=q1 and ?q2.0=q2])
        apply (rule ptrace_postpred_mono[rotated], assumption, blast)
       apply (rule ptrace_postpred_mono[rotated], assumption, blast)
      apply blast
     apply blast
    apply blast
    done
next
  case (rgsat_atom p' r p q q' b F g)
  then show ?case
    by (intro ptrace_atom; blast)
next
  case (rgsat_frame c r g p q F f f')
  then show ?case
    apply (clarsimp simp add: sepconj_conj_def[of p] simp del: sup_apply top_apply)
    apply (rule ptrace_frame[of _ _ _ _ _ _ _ F _ f]; blast)
    done
next
  case (rgsat_weaken c r' g' p' q' F' p q r g F)
  moreover have \<open>p' (hl, hs)\<close>
    using rgsat_weaken.hyps(3) rgsat_weaken.prems
    by (metis rev_predicate1D)
  moreover then have \<open>ptrace c hl hs r' g' q' F'\<close>
    by (simp add: rgsat_weaken.hyps(2))
  ultimately show ?case
    by (meson ptrace_guarantee_mono ptrace_postpred_monoD ptrace_rely_antimonoD ptrace_frameset_antimonoD
        ptrace_frameset_antimonoD)
next
  case (rgsat_Disj P c r g q F n hl hs)
  then show ?case by force
next
  case (rgsat_Conj Q c r g p F n hl hs)
  then show ?case
    by (intro ptrace_Conj'; fast)
qed

end