theory Soundness
  imports RGLogic
begin


section \<open> Operational Semantics \<close>

type_synonym 's pconfig = \<open>'s \<times> 's comm\<close>

type_synonym 's cpconfig = \<open>('s + unit) \<times> 's comm\<close>


subsection \<open> Actions \<close>

datatype 'a act = Tau | Vis 'a

lemma act_not_eq_iff[simp]:
  \<open>\<alpha> \<noteq> Tau \<longleftrightarrow> (\<exists>x. \<alpha> = Vis x)\<close>
  \<open>(\<forall>x. \<alpha> \<noteq> Vis x) \<longleftrightarrow> \<alpha> = Tau\<close>
  by (meson act.distinct act.exhaust)+


subsection \<open> Operational semantics steps \<close>

fun opstep :: \<open>unit act \<Rightarrow> 's pconfig \<Rightarrow> 's cpconfig \<Rightarrow> bool\<close> where
  \<open>opstep \<alpha> (h, Skip) s' \<longleftrightarrow> False\<close>
| \<open>opstep \<alpha> (h, c1 ;; c2) s' \<longleftrightarrow>
    \<alpha> = Tau \<and> c1 = Skip \<and> s' = (Inl h, c2) \<or>
    (\<exists>h' c1'. opstep \<alpha> (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
| \<open>opstep \<alpha> (h, c1 \<^bold>+ c2) s' \<longleftrightarrow>
    \<alpha> = Tau \<and> s' = (Inl h, c1) \<or>
    \<alpha> = Tau \<and> s' = (Inl h, c2)\<close>
| \<open>opstep \<alpha> (h, c1 \<box> c2) s' \<longleftrightarrow>
    \<alpha> \<noteq> Tau \<and> opstep \<alpha> (h, c1) s' \<or>
    \<alpha> \<noteq> Tau \<and> opstep \<alpha> (h, c2) s' \<or>
    \<alpha> = Tau \<and> (\<exists>h' c1'. s' = (h', c1' \<box> c2) \<and> opstep Tau (h, c1) (h', c1')) \<or>
    \<alpha> = Tau \<and> (\<exists>h' c2'. s' = (h', c1 \<box> c2') \<and> opstep Tau (h, c2) (h', c2')) \<or>
    \<alpha> = Tau \<and> c1 = Skip \<and> s' = (Inl h, c2) \<or>
    \<alpha> = Tau \<and> c2 = Skip \<and> s' = (Inl h, c1)\<close>
| \<open>opstep \<alpha> (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    \<alpha> = Tau \<and> c1 = Skip \<and> c2 = Skip \<and> s' = (Inl h, Skip) \<or>
    (\<exists>h' c1'. opstep \<alpha> (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2)) \<or>
    (\<exists>h' c2'. opstep \<alpha> (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2'))\<close>
| \<open>opstep \<alpha> (h, DO c OD) s' \<longleftrightarrow>
      (if \<forall>\<alpha>' s'. \<not> opstep \<alpha>' (h, c) s' then
        \<alpha> = Tau \<and> s' = (Inl h, Skip)
      else
        \<alpha> = Tau \<and> s' = (Inl h, c ;; DO c OD))\<close>
| \<open>opstep \<alpha> (h, Atomic ap aq) s' \<longleftrightarrow>
    (\<exists>a. \<alpha> = Vis a \<and> (if ap h
                  then \<exists>h'. aq h h' \<and> fst s' = Inl h' \<and> snd s' = Skip
                  else fst s' = Inr () \<and> snd s' = Atomic ap aq))\<close>


paragraph \<open> Pretty operational semantics \<close>

abbreviation pretty_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>\<alpha>\<rightarrow> ht \<equiv> opstep \<alpha> hs ht\<close>

abbreviation pretty_no_opstep :: \<open>_ \<Rightarrow> bool\<close> (\<open>_ \<midarrow>|\<rightarrow>\<close> [60] 60) where
  \<open>hs \<midarrow>|\<rightarrow> \<equiv> \<forall>\<alpha> ht. \<not> opstep \<alpha> hs ht\<close>


subsection \<open> Lemmas about opstep \<close>

named_theorems opstep_iff

lemma opstep_tau_preserves_heap:
  assumes \<open>s \<midarrow>Tau\<rightarrow> s'\<close>
  shows \<open>fst s' = Inl (fst s)\<close>
proof -
  { fix \<alpha>
    have \<open>s \<midarrow>\<alpha>\<rightarrow> s' \<Longrightarrow> \<alpha> = Tau \<Longrightarrow> fst s' = Inl (fst s)\<close>
      by (induct \<alpha> s s' rule: opstep.induct) (force split: if_splits)+
  }
  then show ?thesis
    using assms by force
qed

lemma vis_step_impl_atom:
  assumes
    \<open>(s, c) \<midarrow>Vis x\<rightarrow> (z', c')\<close>
  shows
    \<open>\<exists>p q.
      (p, q) \<in> head_atoms c \<and>
      ((p s \<longrightarrow> (\<exists>s'. z' = Inl s' \<and> q s s')) \<and>
        (\<not> p s \<longrightarrow> z' = Inr ()))\<close>
proof -
  { fix \<alpha> sc zc'
    have
      \<open>sc \<midarrow>\<alpha>\<rightarrow> zc' \<Longrightarrow>
        sc = (s, c) \<Longrightarrow>
        zc' = (z', c') \<Longrightarrow>
        \<alpha> = Vis x \<Longrightarrow>
        \<exists>p q.
          (p, q) \<in> head_atoms c \<and>
          ((p s \<longrightarrow> (\<exists>s'. z' = Inl s' \<and> q s s')) \<and>
            (\<not> p s \<longrightarrow> z' = Inr ()))\<close>
      apply (induct \<alpha> sc zc' arbitrary: c s z' c' rule: opstep.induct)
            apply force
           apply (clarsimp; fail)
          apply force
         apply (clarsimp, metis)
        apply (clarsimp, metis)
       apply (clarsimp split: if_splits; fail)
      apply force
      done
  }
  then show ?thesis
    using assms
    by blast
qed

lemma opstep_act_cases:
  \<open>s \<midarrow>\<alpha>\<rightarrow> s' \<Longrightarrow>
    (\<alpha> = Tau \<Longrightarrow> s \<midarrow>Tau\<rightarrow> s' \<Longrightarrow> fst s' = Inl (fst s) \<Longrightarrow> P) \<Longrightarrow>
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

lemma ex_act_neq[simp]:
  \<open>\<exists>\<alpha>. \<alpha> \<noteq> Vis x\<close>
  \<open>\<exists>\<alpha>. \<alpha> \<noteq> Tau\<close>
  by blast+


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

lemma opstep_assert[intro!]:
  \<open>if p h
    then fst s' = Inl h \<and> snd s' = Skip
    else fst s' = Inr () \<and> snd s' = Assert p \<Longrightarrow>
    opstep (Vis ()) (h, Assert p) s'\<close>
  by (force simp add: Assert_def split: if_splits)

lemma opstep_assert_iff[opstep_iff]:
  \<open>opstep \<alpha> (h, Assert p) (h', c') \<longleftrightarrow>
    \<alpha> = Vis () \<and> 
    (if p h
    then h' = Inl h \<and> c' = Skip
    else h' = Inr () \<and> c' = Assert p)\<close>
  by (force simp add: Assert_def split: if_splits)

lemma opstep_assume[intro!]:
  \<open>p h \<Longrightarrow> opstep (Vis ()) (h, Await p) (Inl h, Skip)\<close>
  by (force simp add: Await_def split: if_splits)

lemma opstep_assume_iff[opstep_iff]:
  \<open>opstep \<alpha> (h, Await p) (h', c') \<longleftrightarrow> \<alpha> = Vis () \<and> p h \<and> h' = Inl h \<and> c' = Skip\<close>
  by (force simp add: Await_def split: if_splits)


lemma opstep_IfThenElse_iff[opstep_iff]:
  \<open>opstep \<alpha> (h, IfThenElse p ct cf) s' \<longleftrightarrow>
    \<alpha> = Vis () \<and> p h \<and> s' = (Inl h, Skip ;; ct) \<or>
    \<alpha> = Vis () \<and> \<not> p h \<and> s' = (Inl h, Skip ;; cf)\<close>
  by (simp add: IfThenElse_def Await_def opstep_iff)

lemma opstep_IfThenElse_true[intro]:
  \<open>p h \<Longrightarrow> h' = Inl h \<Longrightarrow> opstep (Vis ()) (h, IfThenElse p a b) (h', Skip ;; a)\<close>
  by (simp add: opstep_iff)

lemma opstep_IfThenElse_false[intro]:
  \<open>\<not> p h \<Longrightarrow> h' = Inl h \<Longrightarrow> opstep (Vis ()) (h, IfThenElse p a b) (h', Skip ;; b)\<close>
  by (simp add: opstep_iff)

lemma opstep_WhileLoop_iff[opstep_iff]:
  \<open>opstep \<alpha> (h, WhileLoop p c) s' \<longleftrightarrow>
    \<alpha> = Tau \<and> p h \<and> s' = (Inl h, (Await p ;; c) ;; DO Await p ;; c OD) \<or>
    \<alpha> = Tau \<and> \<not> p h \<and> s' = (Inl h, Skip)\<close>
  by (force simp add: WhileLoop_def Await_def pre_state_def)


section \<open> Safe \<close>

inductive safe
  :: \<open>nat \<Rightarrow>
      ('l::pre_perm_alg \<times> 's) comm \<Rightarrow>
      'l \<times> 's + unit \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      bool\<close>
  where
  safe_nil[intro!]: \<open>safe 0 c (Inl (hl, hs)) r g q S F\<close>
| safe_suc[intro]:
  \<open>\<comment> \<open> if the command is Skip, the postcondition is established \<close>
    \<comment> \<open> TODO: This requires termination is represented as infinite stuttering past the end.
               We may want a different model, but that would be more complicated. \<close>
    (c = Skip \<longrightarrow> q (hl, hs)) \<Longrightarrow>
    \<comment> \<open> the current state is in the stateset \<close>
    S (hl, hs) \<Longrightarrow>
    \<comment> \<open> rely steps are safe \<close>
    (\<And>hs'. r hs hs' \<Longrightarrow> safe n c (Inl (hl, hs')) r g q S F) \<Longrightarrow>
    \<comment> \<open> closed under framed opsteps \<close>
    (\<And>\<alpha> z' c' hlf.
        hl ## hlf \<Longrightarrow>
        ((hl + hlf, hs), c) \<midarrow>\<alpha>\<rightarrow> (z', c') \<Longrightarrow>
        F (hlf, hs) \<Longrightarrow>
        (\<exists>hlhlf' hs'.
          z' = Inl (hlhlf', hs') \<and>
          (\<alpha> \<noteq> Tau \<longrightarrow> g hs hs') \<and>
          (\<exists>hl'.
            hl' ## hlf \<and>
            hlhlf' = hl' + hlf \<and>
            (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
            S (hl', hs') \<and>
            safe n c' (Inl (hl', hs')) r g q S F))) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe (Suc n) c (Inl (hl, hs)) r g q S F\<close>

subsection \<open> Proofs about safe \<close>

inductive_cases safe_zeroE[elim!]: \<open>safe 0 c s r g q S F\<close>
inductive_cases safe_sucE[elim]: \<open>safe (Suc n) c s r g q S F\<close>

lemma safe_then_state:
  assumes \<open>safe (Suc n) c (Inl (hl, hs)) r g q S F\<close>
  shows \<open>S (hl, hs)\<close>
proof -
  { fix m z
    have \<open>safe m c z r g q S F \<Longrightarrow> 0 < (m::nat) \<Longrightarrow> z = Inl (hl, hs) \<Longrightarrow> S (hl, hs)\<close>
      by (induct rule: safe.inducts) blast+
  } then show ?thesis
    using assms by blast
qed

lemma safe_nil_iff[simp]:
  \<open>safe 0 c s r g q S F \<longleftrightarrow> (\<exists>hl hs. s = Inl (hl, hs))\<close>
  by force

lemma safe_suc_iff:
  \<open>safe (Suc n) c z r g q S F \<longleftrightarrow>
    (\<exists>s. z = Inl s \<and>
      (c = Skip \<longrightarrow> q s) \<and>
      S s \<and>
      (\<forall>hs'. r (snd s) hs' \<longrightarrow> safe n c (Inl (fst s, hs')) r g q S F) \<and>
      (\<forall>\<alpha> z' c' hlf.
          fst s ## hlf \<longrightarrow>
          ((fst s + hlf, snd s), c) \<midarrow>\<alpha>\<rightarrow> (z', c') \<longrightarrow>
          F (hlf, snd s) \<longrightarrow>
          (\<exists>hlhlf' hs'.
            z' = Inl (hlhlf',hs') \<and>
            (\<alpha> \<noteq> Tau \<longrightarrow> g (snd s) hs') \<and>
            (\<exists>hl'.
              hl' ## hlf \<and>
              hlhlf' = hl' + hlf \<and>
              (\<alpha> = Tau \<longrightarrow> hl' = fst s) \<and>
              S (hl', hs') \<and>
              safe n c' (Inl (hl',hs')) r g q S F))))\<close>
  apply (rule iffI)
   apply (erule safe_sucE, (simp; fail))
  apply (force del: safe_suc intro!: safe_suc)
  done

lemma safe_sucD:
  \<open>safe (Suc n) c (Inl (hl, hs)) r g q S F \<Longrightarrow> c = Skip \<Longrightarrow> q (hl, hs)\<close>
  \<open>safe (Suc n) c (Inl (hl, hs)) r g q S F \<Longrightarrow> S (hl, hs)\<close>
  \<open>safe (Suc n) c (Inl (hl, hs)) r g q S F \<Longrightarrow> r hs hs' \<Longrightarrow> safe n c (Inl (hl, hs')) r g q S F\<close>
  \<open>safe (Suc n) c (Inl (hl, hs)) r g q S F \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    ((hl + hlf,hs), c) \<midarrow>\<alpha>\<rightarrow> (z', c') \<Longrightarrow>
    F (hlf, hs) \<Longrightarrow>
    \<exists>hlhlf' hs'.
      z' = Inl (hlhlf',hs') \<and>
      (\<alpha> \<noteq> Tau \<longrightarrow> g hs hs') \<and>
      (\<exists>hl'.
        hl' ## hlf \<and>
        hlhlf' = hl' + hlf \<and>
        (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
        S (hl', hs') \<and>
        safe n c' (Inl (hl', hs')) r g q S F)\<close>
      apply (erule safe_sucE, (simp; metis))+
  done


subsubsection \<open> Monotonicity of safe \<close>

lemma safe_monoD:
  \<open>safe n c s r g q S F \<Longrightarrow>
    m \<le> n \<Longrightarrow>
    q \<le> q' \<Longrightarrow>
    r' \<le> r \<Longrightarrow>
    g \<le> g' \<Longrightarrow>
    F' \<le> F \<Longrightarrow>
    S \<le> S' \<Longrightarrow>
    safe m c s r' g' q' S' F'\<close>
  apply (induct arbitrary: m r' g' q' S' F' rule: safe.induct)
   apply blast
  apply (case_tac m, force)
  apply clarsimp
  apply (rename_tac m)
  apply (rule safe_suc)
     apply fastforce
    apply (metis predicate1D)
   apply (metis (full_types) predicate2D)
  apply (drule meta_spec2, drule meta_spec2, drule meta_mp, assumption, drule meta_mp, assumption)
  apply (drule meta_mp, blast)
  apply clarsimp
  apply (drule spec, drule mp, assumption)+
  apply (metis predicate1D predicate2D)
  done

lemmas safe_mono = safe_monoD[rotated]

lemma safe_step_SucD:
  \<open>safe (Suc n) c s r g q S F \<Longrightarrow> safe n c s r g q S F\<close>
  by (metis safe_monoD[OF _ _ order.refl order.refl order.refl order.refl order.refl]
      le_add2 plus_1_eq_Suc)


subsection \<open> Safety of Skip \<close>

lemma safe_skip_iff:
  \<open>safe n Skip s r g q S F \<longleftrightarrow>
    (\<exists>hl hs. s = Inl (hl, hs) \<and> (\<forall>k<n. \<forall>hs'. (r^^k) hs hs' \<longrightarrow> q (hl, hs') \<and> S (hl, hs')))\<close>
  apply (induct n arbitrary: s)
   apply (simp; fail)
  apply (rule iffI)
   apply (erule safe.cases, blast)
   apply (clarsimp simp add: less_Suc_eq_0_disj)
   apply (metis relpowp_Suc_D2')
  apply clarsimp
  apply (rule safe_suc)
     apply force
    apply force
   apply (clarsimp simp add: less_Suc_eq_0_disj)
   apply (metis relpowp_Suc_I2)
  apply force
  done


lemma safe_skip_stable_iff:
  assumes
    \<open>sswa r S \<le> S\<close>
    \<open>sswa r q \<le> q\<close>
  shows
    \<open>safe n Skip s r g q S F \<longleftrightarrow> (\<exists>hl hs. s = Inl (hl, hs) \<and> (0 < n \<longrightarrow> q (hl, hs) \<and> S (hl, hs)))\<close>
proof -
  have \<open>\<And>n' hl hs.
          (\<forall>k\<le>n'. \<forall>hs'. (r ^^ k) hs hs' \<longrightarrow> q (hl, hs') \<and> S (hl, hs')) \<longleftrightarrow>
            q (hl, hs) \<and> S (hl, hs)\<close>
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
  \<open>wssa r q (hl, hs) \<Longrightarrow> safe n Skip (Inl (hl, hs)) r g q q F\<close>
  apply (induct n arbitrary: hl hs q)
   apply force
  apply (rule safe_suc)
     apply force
    apply force
   apply (simp add: wssa_step; fail)
  apply force
  done

lemma safe_skip:
  \<open>p (hl, hs) \<Longrightarrow> p \<le> wssa r q \<Longrightarrow> q \<le> S \<Longrightarrow> safe n Skip (Inl (hl, hs)) r g q S F\<close>
  apply (rule safe_monoD[OF _ order.refl order.refl order.refl order.refl order.refl])
   apply (rule safe_skip'[where q=\<open>q\<close>])
   apply blast
  apply blast
  done


subsection \<open> Safety of frame \<close>

lemma safe_frame':
  \<open>safe n c s r g q S F \<Longrightarrow>
    s = Inl (hl, hs) \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    sswa (r \<squnion> g) f (hlf, hs) \<Longrightarrow>
    safe n c (Inl (hl + hlf, hs)) r g (q \<^emph>\<and> sswa (r \<squnion> g) f) (S \<^emph>\<and> sswa (r \<squnion> g) f) (sswa (r \<squnion> g) f \<midarrow>\<^emph>\<^sub>\<and> F)\<close>
proof (induct arbitrary: hl hs hlf rule: safe.induct)
  case (safe_nil c ls hs r g q S F)
  then show ?case
    by (metis safe.safe_nil)
next
  case (safe_suc c q lsx hsx S r n g F)

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
      apply (rule hyps(4), blast, blast, blast)
      apply (rule sswa_step, rule sup2I1, blast, blast)
      (* subgoal: local framed opstep *)
    apply (clarsimp simp add: partial_add_assoc2[of hl hlf] simp del: sup_apply)
    apply (rename_tac c hlf2 st')
    apply (frule hyps(5)[rotated 1])
      apply (clarsimp simp add: sepimp_conj_apply simp del: sup_apply)
      apply (metis disjoint_add_leftR disjoint_sym_iff partial_add_commute)
     apply (metis disjoint_add_swap_lr)
    apply (clarsimp simp del: sup_apply)
    apply (rule_tac x=\<open>hl' + hlf\<close> in exI, rule conjI)
     apply (metis disjoint_add_leftR disjoint_add_swap_rl)
    apply (rule conjI)
     apply (metis disjoint_add_leftR partial_add_assoc3)
    apply (clarsimp simp del: sup_apply)
    apply (erule opstep_act_cases)
     apply (simp add: sepconj_conjI; fail)
    apply (frule sswa_stepD, force)
    apply (metis disjoint_add_leftR disjoint_add_rightL sepconj_conjI)
    done
qed

lemma safe_frame:
  \<open>safe n c (Inl (hl, hs)) r g q S F \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    f (hlf, hs) \<Longrightarrow>
    sswa (r \<squnion> g) f \<le> f' \<Longrightarrow>
    F' \<le> sswa (r \<squnion> g) f \<midarrow>\<^emph>\<^sub>\<and> F \<Longrightarrow>
    s = (Inl (hl + hlf, hs)) \<Longrightarrow>
    S \<^emph>\<and> sswa (r \<squnion> g) f \<le> S' \<Longrightarrow>
    safe n c s r g (q \<^emph>\<and> f') S' F'\<close>
  apply simp
  apply (rule safe_monoD[OF _ order.refl _ order.refl order.refl])
     apply (rule safe_frame'[where f=f]; blast)
    apply (simp add: sepconj_conj_mono; fail)
   apply blast
  apply blast
  done


subsection \<open> Safety of Atomic \<close>

lemma safe_atom':
  \<open>\<forall>f\<le>F. wssa r p \<^emph>\<and> f \<le> ap \<Longrightarrow>
    \<forall>f\<le>F. sp aq ((wssa r p) \<^emph>\<and> f) \<le> q \<^emph>\<and> f \<Longrightarrow>
    \<forall>f\<le>F. rel_liftL (wssa r p \<^emph>\<and> f) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    wssa r p (hl, hs) \<Longrightarrow>
    safe n (Atomic ap aq) (Inl (hl, hs)) r g (sswa r q) (wssa r p \<squnion> sswa r q) F\<close>
proof (induct n arbitrary: hl hs)
  case 0 then show ?case by force
next
  case (Suc n)
  show ?case
    using Suc.prems
    apply (intro safe.safe_suc)
      (* subgoal: skip *)
        apply force
      (* subgoal: stateset *)
       apply force
      (* subgoal: rely *)
     apply (rule Suc.hyps)
        apply blast
       apply blast
      apply blast
     apply (meson wssa_step; fail)
      (* subgoal: local framed opstep *)
    apply (clarsimp simp del: sup_apply top_apply simp add: sp_def[of aq])
    apply (clarsimp simp del: all_simps(5) sup_apply simp add: imp_ex_conjL imp_ex imp_conjL le_fun_def)
    apply (drule_tac x=\<open>(=) hlf \<times>\<^sub>P (=) hs\<close> in spec, drule mp, force)
    apply (drule_tac x=\<open>(=) hlf \<times>\<^sub>P (=) hs\<close> in spec, drule mp, force)
    apply (drule_tac x=\<open>(=) hlf \<times>\<^sub>P (=) hs\<close> in spec, drule mp, force)
    apply (subgoal_tac \<open>(p \<^emph>\<and> ((=) hlf \<times>\<^sub>P (=) hs)) (hl + hlf, hs)\<close>)
     prefer 2
     apply (force intro!: sepconj_conjI)
    apply (clarsimp simp add: sepconj_conj_apply imp_ex_conjL imp_conjL simp del: sup_apply)
    apply (simp add: safe_skip_stable_iff sp_sup)
    apply (metis sswa_trivial)
    done
qed

lemma safe_atom:
  \<open>\<forall>f\<le>F. wssa r p \<^emph>\<and> f \<le> ap \<Longrightarrow>
    \<forall>f\<le>F. sp aq (wssa r p \<^emph>\<and> f) \<le> q \<^emph>\<and> f \<Longrightarrow>
    \<forall>f\<le>F. rel_liftL (wssa r p \<^emph>\<and> f) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    wssa r p (hl, hs) \<Longrightarrow>
    sswa r q \<le> q' \<Longrightarrow>
    wssa r p \<le> S \<Longrightarrow>
    sswa r q \<le> S \<Longrightarrow>
    safe n (Atomic ap aq) (Inl (hl, hs)) r g q' S F\<close>
  apply (rule safe_monoD[OF _ order.refl _ order.refl order.refl order.refl])
    apply (rule safe_atom'[where p=\<open>p\<close>]; blast)
   apply (simp; fail)+
  done

lemma single_state_framed_safe_atom':
  \<open>wssa r p \<le> ap \<Longrightarrow>
    \<forall>f. F f \<longrightarrow> p \<^emph>\<and> ((=) f) \<le> ap \<Longrightarrow>
    \<forall>f. F f \<longrightarrow> sp aq (wssa r p \<^emph>\<and> ((=) f)) \<le> q \<^emph>\<and> ((=) f) \<Longrightarrow>
    \<forall>f. F f \<longrightarrow> rel_liftL (wssa r p \<^emph>\<and> ((=) f)) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    wssa r p (hl, hs) \<Longrightarrow>
    safe n (Atomic ap aq) (Inl (hl, hs)) r g (sswa r q) (wssa r p \<squnion> sswa r q) F\<close>
proof (induct n arbitrary: hl hs)
  case 0
  then show ?case by force
next
  case (Suc n)

  show ?case
    using Suc.prems
    apply (intro safe.safe_suc)
      (* subgoal: skip *)
        apply force
      (* subgoal: stateset *)
       apply fastforce
      (* subgoal: rely *)
      apply (rule Suc.hyps; blast intro: wssa_step)
      (* subgoal: local framed opstep *)
    apply (clarsimp simp add: sp_def[of \<open>aq\<close>] le_fun_def imp_conjL imp_ex
        simp del: comp_apply sup_apply top_apply rel_liftL_apply simp del: all_simps(5))
    apply (drule spec2, drule mp[of \<open>F _\<close>], force)
    apply (drule spec2, drule mp[of \<open>F _\<close>], force)
    apply (drule spec2, drule mp[of \<open>F _\<close>], force)
    apply (subgoal_tac \<open>(p \<^emph>\<and> ((=) hlf \<circ> fst)) (hl + hlf, hs)\<close>)
     prefer 2
     apply (force intro!: sepconj_conjI)
    apply (clarsimp simp add: safe_skip_stable_iff sp_sup sepconj_conj_apply
        imp_conjL imp_ex simp del: all_simps(5))
    apply (metis sswa_trivial)
    done
qed


subsection \<open> Safety of Sequencing \<close>

lemma safe_seq_assoc_left:
  \<open>safe n c (Inl (hl, hs)) r g q S F \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe n ((c1 ;; c2) ;; c3) (Inl (hl, hs)) r g q S F\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
     apply blast
    apply blast
   apply blast
  apply clarsimp
  apply (erule disjE, blast)
  apply metis
  done

lemma safe_seq_assoc_right:
  \<open>safe n c (Inl (hl, hs)) r g q S F \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    safe n (c1 ;; c2 ;; c3) (Inl (hl, hs)) r g q S F\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (rule safe_suc)
     apply blast
    apply blast
   apply blast
  apply clarsimp
  apply (erule disjE, blast)
  apply metis
  done

lemma safe_seq':
  \<open>safe n c1 (Inl (hl, hs)) r g q S1 F \<Longrightarrow>
    (\<forall>m\<le>n. \<forall>hl' hs'. q (hl', hs') \<longrightarrow> safe m c2 (Inl (hl', hs')) r g q' S2 F) \<Longrightarrow>
    safe n (c1 ;; c2) (Inl (hl, hs)) r g q' (S1 \<squnion> S2) F\<close>
proof (induct arbitrary: c2 q' rule: safe.inducts)
  case (safe_suc c q hl hs S1 r n g F)

  have safe_c2:
    \<open>\<And>m hl' hs'. m \<le> n \<Longrightarrow> q (hl', hs') \<Longrightarrow> safe m c2 (Inl (hl', hs')) r g q' S2 F\<close>
    \<open>\<And>hl' hs'. q (hl', hs') \<Longrightarrow> safe (Suc n) c2 (Inl (hl', hs')) r g q' S2 F\<close>
    using safe_suc.prems
    by (simp add: le_Suc_eq)+
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
     apply (clarsimp simp del: sup_apply)
     apply (meson le_Suc_eq order_refl safe_monoD safe_suc.hyps(2) sup.cobounded2 sup1CI; fail)
    apply (clarsimp simp del: sup_apply)
    apply (frule(2) safe_suc.hyps(5))
    apply (metis act.distinct(1) safe_c2(1) sup1CI)
    done
qed force


lemma safe_seq:
  \<open>safe n c1 (Inl (hl, hs)) r g q S1 F \<Longrightarrow>
    (\<forall>hl' hs'. q (hl', hs') \<longrightarrow> safe n c2 (Inl (hl', hs')) r g q' S2 F) \<Longrightarrow>
    S1 \<le> S \<Longrightarrow>
    S2 \<le> S \<Longrightarrow>
    safe n (c1 ;; c2) (Inl (hl, hs)) r g q' S F\<close>
  apply (rule safe_monoD[OF _ order.refl order.refl order.refl order.refl order.refl])
   apply (rule safe_seq', blast)
   apply clarsimp
   apply (drule safe_monoD[OF _ _ order.refl order.refl order.refl order.refl],
      assumption, assumption)
   apply (drule spec2, drule mp, assumption)
   apply (rule safe_monoD[OF _ _ order.refl order.refl order.refl order.refl],
      assumption, assumption, assumption)
  apply blast
  done


subsection \<open> Safety of Iter \<close>

lemma safe_iter:
  \<open>(\<And>hl' hs'.
      sswa r i (hl', hs') \<Longrightarrow>
      safe n c (Inl (hl', hs')) r g (sswa r i) (sswa r S) F) \<Longrightarrow>
    sswa r i (hl, hs) \<Longrightarrow>
    safe n (Iter c) (Inl (hl, hs)) r g (sswa r i) (sswa r S) F\<close>
proof (induct n arbitrary: i hl hs S)
  case (Suc n)

  have safe_ih:
    \<open>\<And>m hl' hs'. m \<le> n \<Longrightarrow> sswa r i (hl', hs') \<Longrightarrow> safe m c (Inl (hl', hs')) r g (sswa r i) (sswa r S) F\<close>
    \<open>\<And>hl' hs'. sswa r i (hl', hs') \<Longrightarrow> safe (Suc n) c (Inl (hl', hs')) r g (sswa r i) (sswa r S) F\<close>
    using Suc.prems(1)
    by (force intro: safe_monoD[OF _ _ order.refl order.refl order.refl order.refl order.refl])+

  note safe_suc_c = safe_sucD[OF safe_ih(2)]

  show ?case
    using Suc.prems safe_suc_c(2)[OF Suc.prems(2)]
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: skip *)
       apply blast
      (* subgoal: stateset *)
      apply (simp add: safe_suc_c(2); fail)
      (* subgoal: rely *)
     apply (rule Suc.hyps)
      apply (simp add: safe_ih(1); fail)
     apply (metis sswa_step)
      (* subgoal: locally framed opstep *)
    apply (clarsimp split: if_splits simp add: safe_skip_stable_iff)
    apply (rule safe_seq)
       apply (rule safe_ih(1), blast, blast)
      apply clarsimp
      apply (rule Suc.hyps)
       apply (rule safe_ih(1); blast)
      apply blast
     apply blast
    apply blast
    done
qed force


subsubsection \<open> Safety of internal nondeterminism \<close>

lemma safe_indet':
    \<open>safe n c1 (Inl (hl, hs)) r g q S F \<Longrightarrow>
      safe n c2 (Inl (hl, hs)) r g q S F \<Longrightarrow>
      safe n (c1 \<^bold>+ c2) (Inl (hl, hs)) r g q S F\<close>
proof (induct n arbitrary: c1 c2 hl hs)
  case 0
  then show ?case by blast
next
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
    apply (metis safe_step_SucD safe_then_state)
    done
qed

lemma safe_indet:
  \<open>safe n c1 (Inl (hl, hs)) r g q S1 F \<Longrightarrow>
      safe n c2 (Inl (hl, hs)) r g q S2 F \<Longrightarrow>
      S1 \<squnion> S2 \<le> S \<Longrightarrow>
      safe n (c1 \<^bold>+ c2) (Inl (hl, hs)) r g q S F\<close>
  using safe_indet'
  by (metis le_supE safe_monoD[OF _ order.refl order.refl order.refl order.refl order.refl])


subsubsection \<open> Safety of external nondeterminism \<close>

lemma safe_endet':
    \<open>safe n c1 (Inl (hl, hs)) r g q S F \<Longrightarrow>
      safe n c2 (Inl (hl, hs)) r g q S F \<Longrightarrow>
      safe n (c1 \<box> c2) (Inl (hl, hs)) r g q S F\<close>
proof (induct n arbitrary: c1 c2 hl hs)
  case 0
  then show ?case by blast
next
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
         apply (erule safe_sucE)+
         apply blast
        apply (erule safe_sucE)+
        apply blast
       apply (frule opstep_tau_preserves_heap, clarsimp)
       apply (blast intro: Suc.hyps dest: safe_sucD safe_step_SucD)
      apply (frule opstep_tau_preserves_heap, clarsimp)
      apply (blast intro: Suc.hyps dest: safe_sucD safe_step_SucD)
     apply (blast dest: safe_step_SucD)
    apply (blast dest: safe_step_SucD)
    done
qed

lemma safe_endet:
  \<open>safe n c1 (Inl (hl, hs)) r g q S1 F \<Longrightarrow>
      safe n c2 (Inl (hl, hs)) r g q S2 F \<Longrightarrow>
      S1 \<squnion> S2 \<le> S \<Longrightarrow>
      safe n (c1 \<box> c2) (Inl (hl, hs)) r g q S F\<close>
  using safe_endet'
  by (metis le_supE safe_monoD[OF _ order.refl order.refl order.refl order.refl order.refl])


subsection \<open> Safety of parallel \<close>

lemma safe_parallel':
  \<open>safe n c1 (Inl (hl1, hs)) (r \<squnion> g2) g1 (sswa (r \<squnion> g2) q1) S1 (S2 \<^emph>\<and> F) \<Longrightarrow>
    safe n c2 (Inl (hl2, hs)) (r \<squnion> g1) g2 (sswa (r \<squnion> g1) q2) S2 (S1 \<^emph>\<and> F) \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    safe n (c1 \<parallel> c2) (Inl (hl1 + hl2, hs)) r (g1 \<squnion> g2)
      (sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2)
      (sswa (r \<squnion> g2) S1 \<^emph>\<and> sswa (r \<squnion> g1) S2)
      F\<close>
proof (induct n arbitrary: c1 c2 hl1 hl2 hs)
  case 0 then show ?case by (metis safe_nil_iff)
next
  case (Suc n)

  note safe_suc1 = safe_sucD[OF Suc.prems(1)]
  note safe_suc2 = safe_sucD[OF Suc.prems(2)]
  
  show ?case
  proof (rule safe_suc; fast?; (intro conjI)?)
    show \<open>(sswa (r \<squnion> g2) S1 \<^emph>\<and> sswa (r \<squnion> g1) S2) (hl1 + hl2, hs)\<close>
      using Suc.prems(3) safe_suc1(2) safe_suc2(2)
      by (meson sepconj_conjI sswa_trivial)
  next
    fix hs'
    assume \<open>r hs hs'\<close>
    then show \<open>safe n (c1 \<parallel> c2) (Inl (hl1 + hl2, hs')) r (g1 \<squnion> g2)
            (sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2)
            (sswa (r \<squnion> g2) S1 \<^emph>\<and> sswa (r \<squnion> g1) S2)
            F\<close>
      using Suc.hyps Suc.prems(1-3)
      by blast
  next
    fix \<alpha> c' hlf z'
    assume assms2:
      \<open>hl1 + hl2 ## hlf\<close>
      \<open>opstep \<alpha> ((hl1 + hl2 + hlf, hs), c1 \<parallel> c2) (z', c')\<close>
      \<open>F (hlf, hs)\<close>

    show \<open>\<exists>hlhlf' hs'.
          z' = Inl (hlhlf', hs') \<and>
          (\<alpha> \<noteq> Tau \<longrightarrow> (g1 \<squnion> g2) hs hs') \<and>
          (\<exists>hl'.
            hl' ## hlf \<and>
            hlhlf' = hl' + hlf \<and>
            (\<alpha> = Tau \<longrightarrow> hl' = hl1 + hl2) \<and>
            (sswa (r \<squnion> g2) S1 \<^emph>\<and> sswa (r \<squnion> g1) S2) (hl', hs') \<and>
            safe n c' (Inl (hl', hs')) r (g1 \<squnion> g2) (sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2)
              (sswa (r \<squnion> g2) S1 \<^emph>\<and> sswa (r \<squnion> g1) S2) F)\<close>
      using Suc.prems(3) safe_suc1(2) safe_suc2(2) assms2
      apply (simp add: del: sup_apply)
      apply (elim disjE conjE exE)
        (* subgoal: tau *)
        apply (clarsimp simp del: sup_apply)
        apply (insert safe_suc1(1) safe_suc2(1))
        apply (clarsimp simp del: sup_apply)
        apply (subst safe_skip_stable_iff)
          apply (rule sp_rely_sepconj_conj_semidistrib_mono; force)
         apply (rule sp_rely_sepconj_conj_semidistrib_mono; force)
        apply (clarsimp simp del: sup_apply)
        apply (meson sepconj_conjI sswa_trivial; fail)
        (* subgoal: left *)
       apply (simp add: partial_add_assoc2[of hl1] del: sup_apply)
       apply (frule safe_suc1(4)[rotated])
         apply (meson disjoint_add_leftR disjoint_sym sepconj_conjI sup1I2; fail)
        apply (metis disjoint_add_swap_lr)
       apply (clarsimp simp del: sup_apply)
       apply (rule conjI, blast)
       apply (rule_tac x=\<open>hl' + hl2\<close> in exI)
       apply (intro conjI)
           apply (metis disjoint_add_leftR disjoint_add_swap_rl)
          apply (metis disjoint_add_leftR partial_add_assoc3)
         apply blast
        apply (subgoal_tac \<open>sswa (r \<squnion> g1) S2 (hl2, hs')\<close>)
         prefer 2
         apply (erule opstep_act_cases)
          apply force
         apply (metis (full_types) unit.exhaust sswa_step sswa_trivial sup2I2)
        apply (metis disjoint_add_leftR disjoint_add_rightL sepconj_conjI sswa_trivial)
       apply (rule Suc.hyps)
         apply blast
        apply (erule opstep_act_cases)
         apply (clarsimp simp del: sup_apply)
         apply (meson Suc.prems(2) safe_step_SucD; fail)
        apply (clarsimp simp del: sup_apply)
        apply (blast intro: safe_suc2(3))
       apply (metis disjoint_add_leftR disjoint_add_rightL)
        (* subgoal right *)
      apply (simp add: partial_add_commute[of hl1] partial_add_assoc2[of hl2] disjoint_sym_iff
          del: sup_apply)
      apply (frule safe_suc2(4)[rotated])
        apply (metis disjoint_add_rightR disjoint_sym sepconj_conjI)
       apply (metis disjoint_add_swap_lr disjoint_sym)
      apply (clarsimp simp del: sup_apply)
      apply (rule conjI, blast)
      apply (rule_tac x=\<open>hl' + hl1\<close> in exI)
      apply (intro conjI)
          apply (metis disjoint_add_leftR disjoint_add_swap_rl disjoint_sym)
         apply (metis disjoint_add_leftR partial_add_assoc3 disjoint_sym)
        apply blast
       apply (subgoal_tac \<open>sswa (r \<squnion> g2) S1 (hl1, hs')\<close>)
        prefer 2
        apply (erule opstep_act_cases)
         apply force
        apply (metis (full_types) unit.exhaust sswa_step sswa_trivial sup2I2)
      apply (metis disjoint_add_rightL disjoint_sym_iff partial_add_commute sepconj_conjI
          sswa_trivial)
      apply (simp del: sup_apply add:
          partial_add_commute[of _ hl1, OF disjoint_add_rightL[OF disjoint_add_rightR']])
      apply (rule Suc.hyps)
        apply (erule opstep_act_cases)
         apply (clarsimp simp del: sup_apply)
         apply (metis Suc.prems(1) safe_step_SucD)
        apply (clarsimp simp del: sup_apply)
        apply (blast intro: safe_suc1(3))
       apply blast
      apply (metis disjoint_add_rightL disjoint_add_rightR disjoint_sym)
      done
  qed
qed

lemma safe_parallel:
  \<open>safe n c1 (Inl (hl1, hs)) (r \<squnion> g2) g1 (sswa (r \<squnion> g2) q1) S1 (S2 \<^emph>\<and> F) \<Longrightarrow>
    safe n c2 (Inl (hl2, hs)) (r \<squnion> g1) g2 (sswa (r \<squnion> g1) q2) S2 (S1 \<^emph>\<and> F)  \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2 \<le> q \<Longrightarrow>
    sswa (r \<squnion> g2) S1 \<^emph>\<and> sswa (r \<squnion> g1) S2 \<le> S \<Longrightarrow>
    g1 \<squnion> g2 \<le> g \<Longrightarrow>
    safe n (c1 \<parallel> c2) (Inl (hl1 + hl2, hs)) r g q S F\<close>
  using safe_parallel'
  by (meson safe_monoD[OF _ order.refl _ order.refl _ order.refl])


subsection \<open> Safety of conj \<close>

lemma safe_conj':
  \<open>safe n c (Inl (hl, hs)) r g q1 S F \<Longrightarrow>
    safe n c (Inl (hl, hs)) r g q2 S F \<Longrightarrow>
    \<forall>z a b c. F (c,z) \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    safe n c (Inl (hl, hs)) r g (q1 \<sqinter> q2) S F\<close>
proof (induct n arbitrary: c hl hs r g q1 q2)
  case 0 then show ?case by blast
next
  case (Suc n)

  show ?case
    using Suc.prems
    apply -
    apply (intro safe_suc conjI impI allI)
       apply blast
      apply blast
     apply (rule Suc.hyps; blast)
      (* subgoal: frame safe *)
    apply (clarsimp simp del: inf_apply)
    apply (frule safe_sucD(4)[where q=q1], blast, blast, blast)
    apply (frule safe_sucD(4)[where q=q2], blast, blast, blast)
    apply (erule opstep_act_cases)
     apply (clarsimp simp del: inf_apply)
     apply (rule Suc.hyps; blast)
    apply (clarsimp simp del: inf_apply)
    apply (rename_tac hs' hl'1 hl'2)
    apply (rule exI, rule conjI, assumption, rule conjI, rule refl)
    apply (metis Suc.hyps)
    done
qed

lemma safe_conj:
  \<open>safe n c (Inl (hl, hs)) r g q1 S F \<Longrightarrow>
    safe n c (Inl (hl, hs)) r g q2 S F \<Longrightarrow>
    \<forall>z a b c. F (c,z) \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    safe n c (Inl (hl, hs)) r g (q1 \<sqinter> q2) S F\<close>
  using safe_conj'
  by (rule safe_monoD[OF _ order.refl order.refl order.refl order.refl _ order.refl]) blast+

lemma safe_Conj':
  assumes frame_cancellative:
    \<open>\<forall>z a b f. F (f, z) \<longrightarrow> a ## f \<longrightarrow> b ## f \<longrightarrow> a + f = b + f \<longrightarrow> a = b\<close>
  shows
    \<open>Q \<noteq> {} \<Longrightarrow>
      \<forall>q\<in>Q. safe n c (Inl (hl, hs)) r g q S F \<Longrightarrow>
      safe n c (Inl (hl, hs)) r g (\<Sqinter>Q) S F\<close>
proof (induct n arbitrary: c hl hs r g Q)
  case 0 then show ?case by blast
next
  case (Suc n)

  show ?case
    using Suc.prems
    apply -
    apply (intro safe_suc conjI impI allI)
       apply blast
      apply blast
     apply (rule Suc.hyps, blast, blast)
      (* subgoal(s): framed opstep safe *)
    apply (subgoal_tac \<open>\<exists>q. q \<in> Q\<close>)
     prefer 2
     apply blast
    apply (clarsimp simp del: inf_apply Inf_apply)
    apply (frule_tac q=q in safe_sucD(4)[OF bspec[of _ \<open>\<lambda>q. safe _ _ _ _ _ q _ _\<close>]],
        blast, blast, blast, blast)
    apply (clarsimp simp del: inf_apply Inf_apply)
    apply (subgoal_tac \<open>\<forall>q\<in>Q. safe n c' (Inl (hl', hs')) r g q S F\<close>)
     prefer 2
     apply clarsimp
     apply (drule_tac x=qa in bspec, assumption)
     apply (drule(3) safe_sucD(4))
     apply clarsimp
     apply (cut_tac frame_cancellative)
     apply metis
    apply (metis Suc.hyps)
    done
qed

section \<open> Soundness \<close>

lemma soundness:
  assumes \<open>rgsat c r g p q S F C\<close>
    and \<open>p (hl, hs)\<close>
    and \<open>C = \<top>\<close>
  shows \<open>safe n c (Inl (hl, hs)) r g q S F\<close>
  using assms
proof (induct c r g p q S F C arbitrary: n hl hs rule: rgsat.inducts)
  case (rgsat_skip r p q L C g F)
  then show ?case
    by (intro safe_skip[of p])
      (simp add: wlp_weaker_iff_sp_stronger; fail)+
next
  case (rgsat_iter c r g i L F C p q L')
  then show ?case
    by (intro safe_monoD[OF safe_iter order.refl _ order.refl order.refl order.refl])
      blast+
next
  case (rgsat_seq ca r g p pp La F C cb q Lb L)
  then show ?case
    using safe_seq[of n ca hl hs r g pp La F cb q Lb L]
    by blast
next
  case (rgsat_indet ca r ga p qa La F C cb gb qb Lb g q L)
  then show ?case
    by (intro safe_indet[of n ca hl hs r g q La F cb Lb L])
      (meson order.refl safe_monoD; fail)+
next
  case (rgsat_endet c1 r g1 p q1 L1 F C c2 g2 q2 L2 g q L)
  then show ?case
    by (intro safe_endet[of n c1 hl hs r g q L1 F c2 L2 L])
      (meson order.refl safe_monoD; fail)+
next
  case (rgsat_par c1 r g2 g1 p1 q1 L1 L2 F C c2 p2 q2 g p q L)
  then show ?case
    using safe_parallel[of n c1 _ _ r g2 g1 q1 L1 L2 F c2 _ q2 q L g]
    apply -
    apply (clarsimp simp add: sepconj_conj_def[of p1 p2] le_fun_def[of p]
        simp del: sup_apply top_apply)
    apply (drule spec2, drule mp, blast)
    apply (clarsimp simp del: sup_apply top_apply)
    apply (rule safe_parallel[where ?q1.0=q1 and ?q2.0=q2])
         apply (rule safe_monoD[OF _ order.refl _ order.refl order.refl order.refl order.refl],
        assumption, blast)
        apply (rule safe_monoD[OF _ order.refl _ order.refl order.refl order.refl order.refl],
        assumption, blast)
       apply blast
      apply blast
     apply blast
    apply blast
    done
next
  case (rgsat_atom p' r p q q' L F aq g C ap)
  then show ?case
    by (intro safe_atom[where p=p and q=q]) blast+
next
  case (rgsat_frame c r g p q L F C p' f q' F' L')
  then show ?case
    apply -
    apply (frule(1) predicate1D)
    apply (clarsimp simp del: sup_apply simp add: 
        sepconj_conj_apply)
    apply (rule safe_monoD[OF _ order.refl _ order.refl order.refl order.refl order.refl])
     apply (rule safe_frame[where f=f])
           apply blast
          apply blast
         apply blast
        apply blast
       apply (simp add: sepimp_conj_sepconj_conj_shunt; fail)
      apply blast
     apply (simp add: sepimp_conj_sepconj_conj_shunt)
    apply blast
    done
next
  case (rgsat_weaken c r' g' p' q' L' F' C p q r g L F)
  moreover have \<open>p' (hl, hs)\<close>
    using rgsat_weaken.hyps(3) rgsat_weaken.prems
    by (metis rev_predicate1D)
  moreover then have \<open>safe n c (Inl (hl, hs)) r' g' q' L' F'\<close>
    using rgsat_weaken.prems
    by (fast intro: rgsat_weaken.hyps(2))
  ultimately show ?case
    by (meson safe_monoD[OF _ order.refl])
next
  case (rgsat_Disj p' P c r g q L F C)
  then show ?case
    using Sup1_E by force
next
  case (rgsat_Conj Q c r g p L F C q')
  then show ?case
    by (intro safe_monoD[OF safe_Conj' order.refl _ order.refl order.refl order.refl order.refl])
      blast+
qed

end