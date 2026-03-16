theory Soundness2
  imports "../Soundness"
begin

section \<open> Safe2 \<close>

text \<open>
  Preserve the frame invariant. This is not inductive for the frame rule.
\<close>
inductive safe2
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
  where safe2I[intro]:
    \<open>(c = Skip \<longrightarrow> q s) \<Longrightarrow>
    I s \<Longrightarrow>
    (\<And>n' ss'. n = Suc n' \<Longrightarrow> R (snd s) ss' \<Longrightarrow> safe2 R F G I q n' c (fst s, ss')) \<Longrightarrow>
    (\<And>n' fs \<alpha> lfs' ss' c'.
      n = Suc n' \<Longrightarrow>
      ((fst s + fs, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((lfs', ss'), c') \<Longrightarrow>
      fst s ## fs \<Longrightarrow>
      F (fs, snd s) \<Longrightarrow>
      (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) ss') \<and>
      F (fs, ss') \<and>
      (\<exists>ls'.
        ls' ## fs \<and>
        lfs' = ls' + fs \<and>
        (\<alpha> = Tau \<longrightarrow> ls' = fst s) \<and>
        safe2 R F G I q n' c' (ls', ss'))) \<Longrightarrow>
    safe2 R F G I q n c s\<close>


subsection \<open> Proofs about safe \<close>

inductive_cases safe2_zeroE[elim!]: \<open>safe2 R F G I q 0 c s\<close>
inductive_cases safe2_sucE[elim]: \<open>safe2 R F G I q (Suc n) c s\<close>

lemma safe2_nil_iff[simp]:
  \<open>safe2 R F G I q 0 c s \<longleftrightarrow> (c = Skip \<longrightarrow> q s) \<and> I s\<close>
  by blast

lemma safe2_suc_iff:
  \<open>safe2 R F G I q (Suc n) c s \<longleftrightarrow>
    (c = Skip \<longrightarrow> q s) \<and>
    I s \<and>
    (\<forall>ss'. R (snd s) ss' \<longrightarrow> safe2 R F G I q n c (fst s, ss')) \<and>
    (\<forall>\<alpha> lfs' ss' fs c'.
      ((fst s + fs, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((lfs', ss'), c') \<longrightarrow>
      fst s ## fs \<longrightarrow>
      F (fs, snd s) \<longrightarrow>
      (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) ss') \<and>
      F (fs, ss') \<and>
      (\<exists>ls'.
        ls' ## fs \<and>
        lfs' = ls' + fs \<and>
        (\<alpha> = Tau \<longrightarrow> ls' = fst s) \<and>
        safe2 R F G I q n c' (ls', ss')))\<close>
  apply (rule iffI)
   apply (elim safe2_sucE; simp; fail)
  apply (rule safe2I; force)
  done

lemma safe_sucD:
  \<open>safe2 R F G I q (Suc n) c s \<Longrightarrow> R ss ss' \<Longrightarrow> ss = snd s \<Longrightarrow> safe2 R F G I q n c (fst s, ss')\<close>
  \<open>safe2 R F G I q (Suc n) c s \<Longrightarrow>
    ((fst s + fs, snd s), c) \<midarrow>\<alpha>\<rightarrow> ((slf', ss'), c') \<Longrightarrow>
    fst s ## fs \<Longrightarrow>
    F (fs, snd s) \<Longrightarrow>
    (\<alpha> \<noteq> Tau \<longrightarrow> G (snd s) ss') \<and>
    F (fs, ss') \<and>
    (\<exists>sl'.
      sl' ## fs \<and>
      slf' = sl' + fs \<and>
      (\<alpha> = Tau \<longrightarrow> sl' = fst s) \<and>
      safe2 R F G I q n c' (sl', ss'))\<close>
  by (erule safe2_sucE, (simp; fail))+


subsection \<open> Safety of frame \<close>

text \<open>
  The frame specification is 'lumpy', in that is represents the frames that could possibly
  come from other processes. These do \<^emph>\<open>not\<close> have to be downwards closed. The frame rule is,
  essentially, constructing a 'virtual' process.
    We must assume that the frame specification of the assumption includes not only the sepconj of
  the two elements, but also the frame spec. and frame predicate without any separating conjunction,
  i.e. \<open>F \<^emph>\<and> F' \<squnion> F'\<close>.
\<close>
lemma safe2_frame':
  assumes ni_assms:
    \<open>sswa (R \<squnion> G) F' \<le> F'\<close>
  shows
    \<open>safe2 R (F \<^emph>\<and> F') G I q n c s \<Longrightarrow>
    fst s ## fs \<Longrightarrow>
    F' (fs, snd s) \<Longrightarrow>
    (\<forall>Qa Qb. F \<^emph>\<and> (Qa \<sqinter> Qb) = (F \<^emph>\<and> Qa) \<sqinter> (F \<^emph>\<and> Qb)) \<Longrightarrow>
    safe2 R F G (I \<^emph>\<and> F') (q \<^emph>\<and> F') n c (fst s + fs, snd s)\<close>
proof (induct arbitrary: fs rule: safe2.induct)
  case (safe2I c s n)

  note hyps = safe2I.hyps[simplified safe2I.prems(1)[simplified] fst_conv snd_conv]

  show ?case
    using safe2I.prems(1-2) hyps(1-2)
    apply -
    apply (rule safe2.safe2I)
      (* subgoal: skip *)
       apply (force simp add: sepconj_conj_def simp del: sup_apply)
      (* subgoal: stateset *)
      apply (metis sepconj_conjI surjective_pairing)
      (* subgoal: rely step *)
     apply (simp del: sup_apply top_apply inf_apply)
     apply (rule hyps(4), fast, fast, fast)
     apply (cut_tac ni_assms(1))
     apply (meson predicate1D sswa_step sswa_trivial sup2I1; fail)
      (* subgoal: framed opstep *)
     apply (cut_tac safe2I.prems(3), blast)
    apply (rename_tac n' fsx \<alpha> lfs' ss' c')
    apply (clarsimp simp add: partial_add_assoc2[of \<open>fst s\<close> fs] simp del: sup_apply top_apply)
    apply (frule hyps(5)[rotated 1])
       apply (metis disjoint_add_swap_lr)
      apply (simp add: sepconj_conj_apply)
      apply (metis disjoint_add_leftR disjoint_sym partial_add_commute)
     apply (simp add: disjoint_add_swap_lr; fail)
    apply (clarsimp simp del: top_apply sup_apply inf_apply)
    apply (erule opstep_act_cases)
     apply (metis fst_conv snd_conv partial_add_assoc2 safe2I.prems(3))
    apply (rule conjI)
    subgoal sorry
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

end