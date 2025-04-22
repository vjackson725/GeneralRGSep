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

text \<open>
  The predicate \<open>S\<close> is a command structure predicate. It encompasses the traditional postcondition
    \<open>\<lambda>c s. c = Skip \<longrightarrow> Q s\<close>
  but can be used to specify more complex invariants.
\<close>

inductive safe
  :: \<open>('l \<times> 's \<Rightarrow> 'l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> 'l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> 's) comm \<Rightarrow> 'l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      'l::pre_perm_alg \<Rightarrow>
      's \<Rightarrow>
      ('l \<times> 's) comm \<Rightarrow>
      nat \<Rightarrow>
      bool\<close>
  where
  safe_nil[intro!]: \<open>S c (x, xs) \<Longrightarrow> safe R G S x xs c 0\<close>
| safe_suc[intro]:
  \<open>\<comment> \<open> enforce the command-structure predicate. \<close>
    S c (x, xs) \<Longrightarrow>
    \<comment> \<open> rely steps are safe \<close>
    (\<And>xl xf xf' xs'.
      xl ## xf \<Longrightarrow>
      x = xl + xf \<Longrightarrow>
      R (xf, xs) (xf', xs') \<Longrightarrow>
      xl ## xf' \<Longrightarrow> \<comment> \<open> note how this is an assumption, not a requirement \<close>
      safe R G S (xl + xf') xs' c n) \<Longrightarrow>
    \<comment> \<open> closed under framed opsteps \<close>
    (\<And>\<alpha> mx' c' xl xf.
        ((x, xs), c) \<midarrow>\<alpha>\<rightarrow> (mx', c') \<Longrightarrow>
        prepost_state R (xf, xs) \<Longrightarrow>
        xl ## xf \<Longrightarrow>
        x = xl + xf \<Longrightarrow>
        \<comment> \<open> the local process: \<close>
        (\<exists>xl' xs'.
          \<comment> \<open> must not make the frame incompatible with the environment; \<close>
          xl' ## xf \<and> 
          \<comment> \<open> must not crash; \<close>
          mx' = Inl (xl' + xf, xs') \<and>
          \<comment> \<open> ensures the guarantee with a Vis step, and identical local states with a Tau; and \<close>
          (if \<alpha> = Tau
            then xl' = xl
            else G (xl,xs) (xl',xs')) \<and>
          \<comment> \<open> continues safely. \<close>
          safe R G S (xl' + xf) xs' c' n)) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe R G S x xs c (Suc n)\<close>

subsection \<open> Proofs about safe \<close>

inductive_cases safe_zeroE[elim!]: \<open>safe R G S x xs c 0\<close>
inductive_cases safe_sucE[elim]: \<open>safe R G S x xs c (Suc n)\<close>

lemma safe_then_state:
  assumes \<open>safe R G S x xs c n\<close>
  shows \<open>S c (x, xs)\<close>
  using assms
  by (induct rule: safe.inducts) force+

lemma safe_zero_iff[simp]:
  \<open>safe R G S x xs c 0 \<longleftrightarrow> S c (x, xs)\<close>
  by blast

lemma safe_suc_iff:
  fixes x :: \<open>'l :: pre_perm_alg\<close> and xs :: 's
  shows
  \<open>safe R G S x xs c (Suc n) \<longleftrightarrow>
    S c (x, xs) \<and>
    (\<forall>xl xf xf' xs'.
      xl ## xf \<longrightarrow>
      x = xl + xf \<longrightarrow>
      R (xf, xs) (xf', xs') \<longrightarrow>
      xl ## xf' \<longrightarrow>
      safe R G S (xl + xf') xs' c n) \<and>
    (\<forall>\<alpha> mx' c'.
      ((x, xs), c) \<midarrow>\<alpha>\<rightarrow> (mx', c') \<longrightarrow>
      (\<forall>xl xf.
        xl ## xf \<longrightarrow>
        x = xl + xf \<longrightarrow>
        prepost_state R (xf, xs) \<longrightarrow>
        (\<exists>xl' xs'.
          xl' ## xf \<and>
          mx' = Inl (xl' + xf, xs') \<and>
          (\<alpha> = Tau \<longrightarrow> xl' = xl) \<and>
          (\<alpha> \<noteq> Tau \<longrightarrow> G (xl, xs) (xl',xs')) \<and>
          safe R G S (xl' + xf) xs' c' n)))\<close>
  apply (rule iffI)
   apply (erule safe_sucE, fastforce)
  apply (clarsimp, (rule safe_suc; fastforce))
  done

(*
lemma safe_sucD:
  \<open>safe R G Q (Suc n) c (Inl (hl, hs)) r g q S F \<Longrightarrow> c = Skip \<Longrightarrow> q (hl, hs)\<close>
  \<open>safe R G Q (Suc n) c (Inl (hl, hs)) r g q S F \<Longrightarrow> S (hl, hs)\<close>
  \<open>safe R G Q (Suc n) c (Inl (hl, hs)) r g q S F \<Longrightarrow> r hs hs' \<Longrightarrow> safe n c (Inl (hl, hs')) r g q S F\<close>
  \<open>safe R G Q (Suc n) c (Inl (hl, hs)) r g q S F \<Longrightarrow>
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
        safe n c' (Inl (hl', hs')) r g q S F)\<close>
      apply (erule safe_sucE, (simp; metis))+
  done
*)

subsubsection \<open> Monotonicity of safe \<close>

\<comment> \<open> TODO: move \<close>
lemma prepost_state_rel_mono:
  \<open>r \<le> r' \<Longrightarrow> prepost_state r x \<Longrightarrow> prepost_state r' x\<close>
  by (simp add: prepost_state_def', blast)

lemma safe_monoD:
  assumes
    \<open>safe R G S x xs c n\<close>
    \<open>S \<le> S'\<close>
    \<open>G \<le> G'\<close>
    \<open>R' \<le> R\<close>
    \<open>n' \<le> n\<close>
  shows
    \<open>safe R' G' S' x xs c n'\<close>
  using assms
  apply -
  apply (induct arbitrary: R' G' S' n' rule: safe.induct)
   apply blast
  apply (case_tac n')
   apply (auto; fail)[1]
  apply clarsimp
  apply (rule safe_suc)
    apply (meson predicate2D; fail)
   apply blast
  apply (clarsimp split: if_splits)
  apply (drule_tac x=\<alpha> in meta_spec2, drule meta_spec2, drule meta_spec,
      drule meta_mp, assumption)
  apply (drule meta_mp, rule prepost_state_rel_mono[rotated], assumption)
   apply blast
  apply (case_tac \<alpha>, force)
  apply clarsimp
  apply (metis (no_types) predicate2D)
  done

lemmas safe_mono = safe_monoD[rotated]


subsection \<open> Safety of Skip \<close>

\<comment> \<open> TODO: move \<close>
lemma all_assm_all_assm_exch:
  \<open>(\<forall>x. P x \<longrightarrow> (\<forall>y. Q y \<longrightarrow> f x y)) \<longleftrightarrow> (\<forall>y. Q y \<longrightarrow> (\<forall>x. P x \<longrightarrow> f x y))\<close>
  by blast

lemma safe_skip_iff:
  fixes xl :: \<open>'l::pre_perm_alg\<close> and xs :: 's
  shows
  \<open>safe R G S x xs Skip n \<longleftrightarrow>
    (\<forall>k\<le>n. \<forall>z zs.
        rgsep_iter (rely_fluff R) k (x, xs) (z, zs) \<longrightarrow> S Skip (z, zs))\<close>
proof (induct n arbitrary: x xs)
  case 0 then show ?case by force
next
  case (Suc n)

  show ?case
    apply (clarsimp simp add: safe_suc_iff)
    apply (subst Suc.hyps)
    apply (clarsimp simp add: le_Suc_iff0 safe_suc_iff imp_ex_conjL imp_conjL all_conj_distrib)
    apply fast
    done
qed


lemma safe_skip_stable_iff:
  assumes \<open>sswa_rely R (S Skip) \<le> S Skip\<close>
  shows \<open>safe R G S x xs Skip n \<longleftrightarrow> S Skip (x, xs)\<close>
  using assms
  by (force simp add: safe_skip_iff wlp_def rgsep_star_def)

lemma safe_skip':
  assumes \<open>wssa_rely R (S Skip) (x, xs)\<close>
  shows \<open>safe R G S x xs Skip n\<close>
  using assms
  by (force simp add: safe_skip_iff wlp_def rgsep_star_def)

lemma safe_skip:
  \<open>P (x, xs) \<Longrightarrow> sswa_rely R P \<le> (S Skip) \<Longrightarrow> safe R G S x xs Skip n\<close>
  by (force simp add: safe_skip_iff sp_def rgsep_star_def le_fun_def)


subsection \<open> Safety of frame \<close>

definition
  \<open>guar_frame G F \<equiv>
    \<lambda>(xlf, s) (xlf', s').
      (\<forall>xl xl' f.
        F f \<longrightarrow>
        xl ## f \<longrightarrow> xlf = xl + f \<longrightarrow>
        xl' ## f \<longrightarrow> xlf' = xl' + f \<longrightarrow>
        G (xl, s) (xl', s'))\<close>

definition
  \<open>rely_frame G F \<equiv>
    \<lambda>(fab, s) (fab', s').
      (\<exists>fa. F fa \<and>
        (\<exists>fb. fa ## fb \<and> fab = fa + fb \<and>
          (\<exists>fb'. fa ## fb' \<and> fab' = fa + fb' \<and>
            G (fb, s) (fb', s'))))\<close>

lemma guar_frame_apply[simp]:
  \<open>guar_frame G F (xla, xs) (xla', xs') \<longleftrightarrow>
    (\<forall>fa xl xl'. F fa \<longrightarrow> xl ## fa \<longrightarrow> xl' ## fa \<longrightarrow> G (xl, xs) (xl', xs'))\<close>
  by (simp add: guar_frame_def)

lemma rely_frame_apply[simp]:
  \<open>rely_frame R F (fab, s) (fab', s') \<longleftrightarrow>
    (\<exists>fa. F fa \<and>
      (\<exists>fb. fa ## fb \<and> fab = fa + fb \<and>
        (\<exists>fb'. fa ## fb' \<and> fab' = fa + fb' \<and>
          R (fb, s) (fb', s'))))\<close>
  by  (simp add: rely_frame_def)

lemma prepost_rely_frame_then:
  \<open>prepost_state (rely_frame R F) (fab, s) \<Longrightarrow>
    (\<exists>fa fb. fa ## fb \<and> fab = fa + fb \<and> prepost_state R (fb, s) \<and> F fa)\<close>
  by (simp add: rely_frame_def prepost_state_def', fast)

(*
lemma safe_frame':
  \<open>safe R G S x xs c n \<Longrightarrow>
    safe (rely_frame R F) (guar_frame G F) S x xs c n\<close>
proof (induct rule: safe.induct)
  case safe_nil
  then show ?case by force
next
  case (safe_suc S c x xs R G n)

  show ?case
    apply -
    apply (rule safe.safe_suc)
      (* subgoal: state pred *)
      apply (cut_tac safe_suc.hyps(1))
      apply force
      (* subgoal: env step *)
     apply clarsimp
     apply (rename_tac xl xs' fa fb fb')
     apply (subgoal_tac \<open>xl + (fa + fb') = xl + fa + fb'\<close>)
      prefer 2
    subgoal sorry
     apply simp
     apply (rule_tac safe_suc.hyps(3)[rotated 2], assumption)
       apply (simp add: disjoint_add_swap_rl; fail)
      apply (simp add: disjoint_add_swap_rl; fail)
    subgoal sorry
      (* subgoal: local framed opstep *)
    apply (frule prepost_rely_frame_then)
    apply (elim exE conjE)
    apply (frule_tac xl=\<open>xl + fa\<close> in safe_suc.hyps(4))
       apply blast
      apply clarsimp
    subgoal sorry
     apply (simp add: partial_add_assoc3; fail)
    apply (clarsimp split: if_splits)
    apply (rule_tac x=xl in exI)
    apply (rule conjI)
    subgoal sorry
    apply (case_tac \<alpha>)
     apply (simp add: partial_add_assoc3; fail)
    apply clarsimp
    apply (intro conjI)
      prefer 2

    sorry

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
  apply (rule safe_postpred_monoD)
   apply (rule safe_frameset_antimonoD)
    apply (rule safe_stateset_monoD)
     apply (rule safe_frame'[where f=f]; blast)
    apply blast
   apply blast
  apply (blast dest: sepconj_conj_monoR)
  done
*)

(*
subsection \<open> Safety of Atomic \<close>

lemma safe_atom':
  \<open>\<forall>f\<le>F. wssa r p \<^emph>\<and> f \<le> ap \<Longrightarrow>
    \<forall>f\<le>F. sp aq ((wssa r p) \<^emph>\<and> f) \<le> q \<^emph>\<and> f \<Longrightarrow>
    \<forall>f\<le>F. rel_liftL (wssa r p \<^emph>\<and> f) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
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
  apply (rule safe_postpred_mono, assumption)
  apply (rule safe_stateset_monoD)
   apply (rule safe_atom'[where p=\<open>p\<close>]; blast)
  apply (simp; fail)
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
    \<open>\<And>hl' hs'. q (hl', hs') \<Longrightarrow> safe R G Q (Suc n) c2 (Inl (hl', hs')) r g q' S2 F\<close>
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
     apply (meson order.refl inf_sup_ord(4) safe_c2(1) safe_stateset_monoD; fail)
    apply (clarsimp simp del: sup_apply)
    apply (frule(2) safe_suc.hyps(5))
    apply (metis act.distinct(1) safe_c2(1))
    done
qed force


lemma safe_seq:
  \<open>safe n c1 (Inl (hl, hs)) r g q S1 F \<Longrightarrow>
    (\<forall>hl' hs'. q (hl', hs') \<longrightarrow> safe n c2 (Inl (hl', hs')) r g q' S2 F) \<Longrightarrow>
    S1 \<le> S \<Longrightarrow>
    S2 \<le> S \<Longrightarrow>
    safe n (c1 ;; c2) (Inl (hl, hs)) r g q' S F\<close>
  apply (rule safe_stateset_monoD)
   apply (rule safe_seq')
    apply blast
   apply clarsimp
   apply (drule safe_step_monoD[rotated, where S=S2])
    apply blast
   apply blast
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
    \<open>\<And>hl' hs'. sswa r i (hl', hs') \<Longrightarrow> safe R G Q (Suc n) c (Inl (hl', hs')) r g (sswa r i) (sswa r S) F\<close>
    using Suc.prems(1)
    by (force intro: safe_step_monoD)+

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
    apply (metis safe_step_SucD)
    done
qed

lemma safe_indet:
  \<open>safe n c1 (Inl (hl, hs)) r g q S1 F \<Longrightarrow>
      safe n c2 (Inl (hl, hs)) r g q S2 F \<Longrightarrow>
      S1 \<squnion> S2 \<le> S \<Longrightarrow>
      safe n (c1 \<^bold>+ c2) (Inl (hl, hs)) r g q S F\<close>
  using safe_indet'
  by (metis le_supE safe_stateset_monoD)


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
         apply (blast dest: safe_sucD)
        apply (blast dest: safe_sucD)
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
  by (metis le_supE safe_stateset_monoD)


subsection \<open> Safety of parallel \<close>

lemma safe_parallel':
  \<open>safe n c1 (Inl (hl1, hs)) (r \<squnion> g2) g1 (sswa (r \<squnion> g2) q1) S1 (S2 \<squnion> S2 \<^emph>\<and> F) \<Longrightarrow>
    safe n c2 (Inl (hl2, hs)) (r \<squnion> g1) g2 (sswa (r \<squnion> g1) q2) S2 (S1 \<squnion> S1 \<^emph>\<and> F) \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    safe n (c1 \<parallel> c2) (Inl (hl1 + hl2, hs)) r (g1 \<squnion> g2)
      (sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2)
      (sswa (r \<squnion> g2) S1 \<^emph>\<and> sswa (r \<squnion> g1) S2)
      F\<close>
proof (induct n arbitrary: c1 c2 hl1 hl2 hs)
  case 0
  then show ?case
    by (metis Inl_inject comm.distinct(3) safe_nil_iff sepconj_conjI sswa_trivial)
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
          (\<exists>hl'. hl' ## hlf \<and>
                 hlhlf' = hl' + hlf \<and>
                 (\<alpha> = Tau \<longrightarrow> hl' = hl1 + hl2) \<and>
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
        apply (metis disjoint_add_rightR disjoint_sym sepconj_conjI sup1CI)
       apply (metis disjoint_add_swap_lr disjoint_sym)
      apply (clarsimp simp del: sup_apply)
      apply (rule conjI, blast)
      apply (rule_tac x=\<open>hl' + hl1\<close> in exI)
      apply (intro conjI)
         apply (metis disjoint_add_leftR disjoint_add_swap_rl disjoint_sym)
        apply (metis disjoint_add_leftR partial_add_assoc3 disjoint_sym)
       apply blast
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
  \<open>safe n c1 (Inl (hl1, hs)) (r \<squnion> g2) g1 (sswa (r \<squnion> g2) q1) S1 (S2 \<squnion> S2 \<^emph>\<and> F) \<Longrightarrow>
    safe n c2 (Inl (hl2, hs)) (r \<squnion> g1) g2 (sswa (r \<squnion> g1) q2) S2 (S1 \<squnion> S1 \<^emph>\<and> F)  \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2 \<le> q \<Longrightarrow>
    sswa (r \<squnion> g2) S1 \<^emph>\<and> sswa (r \<squnion> g1) S2 \<le> S \<Longrightarrow>
    g1 \<squnion> g2 \<le> g \<Longrightarrow>
    safe n (c1 \<parallel> c2) (Inl (hl1 + hl2, hs)) r g q S F\<close>
  using safe_parallel'
  by (meson safe_guarantee_monoD safe_stateset_monoD safe_postpred_mono)


subsection \<open> Safety of conj \<close>

lemma safe_conj':
  \<open>safe n c (Inl (hl, hs)) r g q1 S F \<Longrightarrow>
    safe n c (Inl (hl, hs)) r g q2 S F \<Longrightarrow>
    \<forall>z a b c. F (c,z) \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    safe n c (Inl (hl, hs)) r g (q1 \<sqinter> q2) S F\<close>
proof (induct n arbitrary: c hl hs r g q1 q2)
  case 0
  then show ?case by blast
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
    apply (rule Suc.hyps; blast)
    done
qed

lemma safe_conj:
  \<open>safe n c (Inl (hl, hs)) r g q1 S F \<Longrightarrow>
    safe n c (Inl (hl, hs)) r g q2 S F \<Longrightarrow>
    \<forall>z a b c. F (c,z) \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    safe n c (Inl (hl, hs)) r g (q1 \<sqinter> q2) S F\<close>
  using safe_conj'
  by (rule safe_frameset_antimonoD) blast+

lemma safe_Conj':
  assumes frame_cancellative:
    \<open>\<forall>z a b f. F (f, z) \<longrightarrow> a ## f \<longrightarrow> b ## f \<longrightarrow> a + f = b + f \<longrightarrow> a = b\<close>
  shows
    \<open>Q \<noteq> {} \<Longrightarrow>
      \<forall>q\<in>Q. safe n c (Inl (hl, hs)) r g q S F \<Longrightarrow>
      safe n c (Inl (hl, hs)) r g (\<Sqinter>Q) S F\<close>
proof (induct n arbitrary: c hl hs r g Q)
  case 0
  then show ?case by blast
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
*)


section \<open> Soundness \<close>

lemma soundness:
  assumes \<open>rgsat c r g p q S F\<close>
    and \<open>p (hl, hs)\<close>
  shows \<open>safe R G S (hl + F) xs c n\<close>
  using assms
proof (induct c r g p q S F arbitrary: n hl hs rule: rgsat.inducts)
  case (rgsat_skip r p q S g F)
  then show ?case
    by (simp add: safe_skip)
next
  case (rgsat_iter c r g i S F p q S')
  then show ?case
    apply -
    apply (rule safe_stateset_monoD[rotated], assumption)
    apply (rule safe_postpred_monoD[rotated], assumption)
    apply (rule safe_iter)
     apply blast
    apply blast
    done
next
  case (rgsat_seq c1 r g p1 p2 S1 F c2 p3 S2 S)
  then show ?case
    using safe_seq[of n c1 hl hs r g p2 S1 F c2 p3 S2 S]
    by blast
next
  case (rgsat_indet c1 r g1 p q1 S1 F c2 g2 q2 S2 g q S)
  then show ?case
    using safe_indet[of n c1 hl hs r g q S1 F c2 S2 S]
    by (meson safe_guarantee_mono safe_postpred_mono)
next
  case (rgsat_endet c1 r g1 p q1 S1 F c2 g2 q2 S2 g q S)
  then show ?case
    using safe_endet[of n c1 hl hs r g q S1 F c2 S2 S]
    by (meson safe_guarantee_mono safe_postpred_mono)
next
  case (rgsat_par c1 r g2 g1 p1 q1 S1 S2 F c2 p2 q2 g p q S n)
  then show ?case
    using safe_parallel[of n c1 _ _ r g2 g1 q1 S1 S2 F c2 _ q2 q S g]
    apply -
    apply (clarsimp simp add: sepconj_conj_def[of p1 p2] le_fun_def[of p]
        simp del: sup_apply top_apply)
    apply (drule spec2, drule mp, blast)
    apply (clarsimp simp del: sup_apply top_apply)
    apply (rule safe_parallel[where ?q1.0=q1 and ?q2.0=q2])
         apply (rule safe_postpred_mono[rotated], assumption, blast)
        apply (rule safe_postpred_mono[rotated], assumption, blast)
       apply blast
      apply blast
     apply blast
    apply blast
    done
next
  case (rgsat_atom p' r p q q' S F ap aq g)
  then show ?case
    by (intro safe_atom[where p=p and q=q]; blast)
next
  case (rgsat_frame c r g p q S F p' f q' F' S')
  then show ?case
    apply -
    apply (frule(1) predicate1D)
    apply (clarsimp simp del: sup_apply simp add: 
        sepconj_conj_apply)
    apply (rule safe_postpred_mono[OF _ safe_frame[where f=f]])
           apply blast
          apply blast
         apply blast
        apply blast
       apply blast
      apply (simp add: sepimp_conj_sepconj_conj_shunt; fail)
     apply blast
    apply (simp add: sepimp_conj_sepconj_conj_shunt)
    done
next
  case (rgsat_weaken c r' g' p' q' F' S' p q r g F S)
  moreover have \<open>p' (hl, hs)\<close>
    using rgsat_weaken.hyps(3) rgsat_weaken.prems
    by (metis rev_predicate1D)
  moreover then have \<open>safe n c (Inl (hl, hs)) r' g' q' F' S'\<close>
    using rgsat_weaken.prems
    by (simp add: rgsat_weaken.hyps(2))
  ultimately show ?case
    by (meson safe_stateset_monoD safe_frameset_antimonoD safe_postpred_mono
        safe_rely_antimono safe_guarantee_mono)
next
  case (rgsat_Disj p' P c r g q S F)
  then show ?case
    using Sup1_E by force
next
  case (rgsat_Conj Q c r g p F q')
  then show ?case
    by (simp add: safe_Conj' safe_postpred_mono)
qed

end