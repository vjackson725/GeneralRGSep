theory TreeSem
  imports Soundness "HOL-Cardinals.Bounded_Set"
begin

section \<open> utils \<close>

lemma disjCE:
  \<open>P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not> P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R\<close>
  by blast


section \<open> Bounded Set Utils \<close>

lemma bmember_bmap_iff:
  \<open>bmember y (map_bset f B) \<longleftrightarrow> (\<exists>x. bmember x B \<and> y = f x)\<close>
  by transfer (force simp add: image_def)

lemma bCollect_eq_bempty_iff[simp]:
  \<open>bCollect p = bempty \<longleftrightarrow> (\<nexists>x. p x)\<close>
  by (metis Collect_empty_eq bCollect.rep_eq bempty.rep_eq set_bset_inject)

lemma pred_bset_bempty[simp]:
  \<open>pred_bset p bempty\<close>
  by (simp add: bset.pred_rel)

lemma pred_bCollect_eq[simp]:
  \<open>pred_bset p (bCollect q) = (q \<le> p)\<close>
  by (simp add: bCollect.rep_eq bset.pred_set le_fun_def)

declare bempty.rep_eq[simp]
declare map_bset.rep_eq[simp]
declare bCollect.rep_eq[simp]


section \<open> Semantic Trees \<close>

datatype 'a label = Env | Local \<open>'a act\<close>

datatype ('c, 's, 'l) sem_tree =
  Branch
    (comm_sem_tree: 'c)
    \<comment> \<open> This stores every framed state greater than some base state. \<close>
    (branches_sem_tree:
      \<open>('s \<times> 'l \<times> (('s \<times> ('c, 's, 'l) sem_tree) + unit)) set[('s \<times> 'l \<times> (('s + unit) \<times> 'c)) set]\<close>)

lemma sem_tree_induct:
  \<open>(\<And>ty.
      (\<And>s l s' tx.
        (s, l, Inl (s', tx)) \<in> set_bset (branches_sem_tree ty) \<Longrightarrow>
        P tx) \<Longrightarrow>
      P ty) \<Longrightarrow>
    P t\<close>
  apply (rule sem_tree.induct)
  apply (clarsimp simp add: image_def Bex_def)
  apply fastforce
  done

function pred_sem_tree
  :: \<open>('c \<Rightarrow>
        ('s \<times> 'l \<times> (('s \<times> ('c, 's, 'l) sem_tree) + unit)) set[('s \<times> 'l \<times> (('s + unit) \<times> 'c)) set] \<Rightarrow>
        bool) \<Rightarrow>
      ('c, 's, 'l) sem_tree \<Rightarrow>
      bool\<close>
  where
  \<open>pred_sem_tree p (Branch c S) =
    (p c S \<and>
      pred_bset (\<lambda>v. case v of (s,l,mst') \<Rightarrow> case_sum (pred_sem_tree p \<circ> snd) (\<lambda>_. True) mst') S)\<close>
  by pat_completeness auto
termination
  apply (relation
      \<open>{((xa,ta),(xb,tb)).
          xa = xb \<and> (\<exists>s l s'. (s, l, Inl (s', ta)) \<in> set_bset (branches_sem_tree tb))}\<close>)
   apply (clarsimp simp add: wf_def, rule sem_tree_induct, blast)
  apply force
  done




definition config_pred_sem_tree :: \<open>('c \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('c, 's, 'l) sem_tree \<Rightarrow> bool\<close> where
  \<open>config_pred_sem_tree p t \<equiv>
    pred_sem_tree (\<lambda>c S. \<forall>s l mst'. (s,l,mst') \<in> set_bset S \<longrightarrow> p c s) t\<close>

definition precond_pred_sem_tree :: \<open>('s set \<Rightarrow> bool) \<Rightarrow> ('c, 's, 'l) sem_tree \<Rightarrow> bool\<close> where
  \<open>precond_pred_sem_tree P t \<equiv> pred_sem_tree (\<lambda>_ S. P (fst ` set_bset S)) t\<close>

definition step_rel_sem_tree :: \<open>('l \<Rightarrow> 's \<Rightarrow> 's + unit \<Rightarrow> bool) \<Rightarrow> ('c, 's, 'l) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>step_rel_sem_tree r t =
      pred_sem_tree (\<lambda>c S. \<forall>s l mst'. (s,l,mst') \<in> set_bset S \<longrightarrow> r l s (map_sum fst id mst')) t\<close>

definition steps_pred_sem_tree
  :: \<open>(('s \<times> 'l \<times> ('s + unit)) set \<Rightarrow> bool) \<Rightarrow> ('c, 's, 'l) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>steps_pred_sem_tree P t \<equiv>
      pred_sem_tree
        (\<lambda>_ S. P (set_bset (map_bset (\<lambda>(s, l, mst'). (s, l, map_sum fst id mst')) S)))
        t\<close>

(*
definition
  \<open>sem_tree_contains t1 t2 \<equiv>
    (t1, t2) \<in> {(t1,t2). t1 \<in> snd ` set_bset (branches_sem_tree t2)}\<^sup>+\<close>

lemmas sem_tree_contains_baseI =
  r_into_trancl[
    of _ _ \<open>{(t1,t2). t1 \<in> snd ` set_bset (branches_sem_tree t2)}\<close>,
    simplified,
    simplified sem_tree_contains_def[symmetric]]

lemmas sem_tree_contains_stepI =
  trancl_into_trancl[
    of _ _ \<open>{(t1,t2). t1 \<in> snd ` set_bset (branches_sem_tree t2)}\<close>,
    simplified,
    simplified sem_tree_contains_def[symmetric]]

lemmas sem_tree_contains_induct =
  trancl.induct[
    of _ _ \<open>{(t1,t2). t1 \<in> snd ` set_bset (branches_sem_tree t2)}\<close>,
    simplified,
    simplified sem_tree_contains_def[symmetric]]

lemmas sem_tree_containsE[elim] =
  trancl.cases[
    of _ _ \<open>{(t1,t2). t1 \<in> snd ` set_bset (branches_sem_tree t2)}\<close>,
    simplified,
    simplified sem_tree_contains_def[symmetric]]

lemma sem_tree_contains_branches_no_loop:
  \<open>sem_tree_contains a b \<Longrightarrow>
    b \<notin> snd ` set_bset (branches_sem_tree a)\<close>
  by (induct b arbitrary: a rule: sem_tree_induct)
    (meson sem_tree_containsE sem_tree_contains_baseI trancl_trans
      sem_tree_contains_def)

lemma sem_tree_contains_no_loop:
  \<open>sem_tree_contains a b \<Longrightarrow> \<not> sem_tree_contains b a\<close>
  by (erule sem_tree_contains_induct)
    (meson sem_tree_contains_branches_no_loop sem_tree_contains_def trancl_trans)+
*)



fun bounded_treesem
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's, unit) comm \<Rightarrow>
      'l \<times> 's \<Rightarrow>
      nat \<Rightarrow>
      (('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree\<close>
  where
  \<open>bounded_treesem r F c s 0 = Branch c bempty\<close>
| \<open>bounded_treesem r F c (hl,hs) (Suc n) =
    Branch c
      (map_bset
        (apsnd (apsnd (\<lambda>(z', c'). (map_sum (\<lambda>s'. (s', bounded_treesem r F c' s' n)) id z'))))
        (bCollect
          (\<lambda>((hlx,hsx), l, (z', c')).
              hsx = hs \<and> (
                (hlx = hl \<or> (\<exists>hlf. F (hlf, hsx) \<and> hl ## hlf \<and> hlx = hl + hlf)) \<and>
                  (\<exists>\<alpha>. l = Local \<alpha> \<and> ((hlx,hsx), c) \<midarrow>\<alpha>\<rightarrow> (z', c')) \<or>
                (hlx = hl \<and> c' = c \<and> (\<exists>hsx'. l = Env \<and> r hsx hsx' \<and> z' = Inl (hlx, hsx')))))))\<close>

lemma precond_pred_sem_tree_mono:
  \<open>p \<le> q \<Longrightarrow> pred_sem_tree p t \<Longrightarrow> pred_sem_tree q t\<close>
  apply (induct t)
  apply (clarsimp split: prod.splits)
  apply (rule conjI, blast)
  apply (rule bset.pred_mono_strong, assumption)
  apply (clarsimp split: sum.splits)
  done

lemmas precond_pred_sem_tree_monoD = precond_pred_sem_tree_mono[rotated]

(*
definition treesem
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's, unit) comm \<Rightarrow>
      (('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree set\<close> where
  \<open>treesem r c \<equiv> range (bounded_treesem r c)\<close>
*)


definition sem_tree_nocrash
  :: \<open>(('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>sem_tree_nocrash \<equiv> step_rel_sem_tree (\<lambda>_ _ z'. z' \<noteq> Inr ())\<close>

definition sem_tree_post
  :: \<open>('s \<Rightarrow> bool) \<Rightarrow> (('s, unit) comm, 's, unit label) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>sem_tree_post q \<equiv> config_pred_sem_tree (\<lambda>c s. c = Skip \<longrightarrow> q s)\<close>

definition sem_tree_guar
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> (('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>sem_tree_guar g \<equiv>
      step_rel_sem_tree (\<lambda>l s z'. \<forall>\<alpha> s'. l = Local \<alpha> \<longrightarrow> z' = Inl s' \<longrightarrow> g (snd s) (snd s'))\<close>

definition sem_tree_states
  :: \<open>('l \<times> 's \<Rightarrow> bool) \<Rightarrow> (('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>sem_tree_states S \<equiv> config_pred_sem_tree (\<lambda>_. S)\<close>

definition sem_tree_frame_cond
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow>
      bool\<close>
  where
  \<open>sem_tree_frame_cond F \<equiv>
    steps_pred_sem_tree (\<lambda>S.
      \<forall>\<alpha> hl hs hl' hs'.
        ((hl, hs), Local \<alpha>, (Inl (hl', hs'))) \<in> S \<longrightarrow>
        (\<forall>hlf hlhlf'.
          F (hlf, hs) \<longrightarrow>
          hl ## hlf \<longrightarrow>
          ((hl + hlf, hs), Local \<alpha>, (Inl (hlhlf', hs'))) \<in> S \<longrightarrow>
          (\<exists>hl'. hl' ## hlf \<and> hlhlf' = hl' + hlf)))\<close>


definition sem_tree_safe
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow>
      bool\<close>
  where
  \<open>sem_tree_safe q g S \<equiv>
    sem_tree_nocrash \<sqinter>
    sem_tree_post q \<sqinter>
    sem_tree_guar g \<sqinter>
    sem_tree_states S\<close>


lemma safe_then_sem_tree_safe:
  \<open>safe n c z r g q S F \<Longrightarrow>
    z = Inl s \<Longrightarrow>
    sem_tree_safe q g S (bounded_treesem r F c s n)\<close>
  apply (induct arbitrary: s rule: safe.inducts)
  sorry

lemma sem_tree_safe_then_safe:
  \<open>sem_tree_safe q g S (bounded_treesem r F (s, c) n) \<Longrightarrow>
    safe n c (Inl s) r g q S F\<close>
  apply (induct n arbitrary: s c)
  sorry

theorem safe_iff_sem_tree_safe:
  \<open>safe n c (Inl s) r g q S F \<longleftrightarrow> sem_tree_safe q g S (bounded_treesem r F (s, c) n)\<close>
  using safe_then_sem_tree_safe sem_tree_safe_then_safe
  by fast


end