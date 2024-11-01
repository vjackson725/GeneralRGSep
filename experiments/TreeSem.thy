theory TreeSem
  imports "../Soundness" "HOL-Cardinals.Bounded_Set" "HOL-Library.BNF_Corec"
begin

lemma bmember_bmap_iff:
  \<open>bmember y (map_bset f B) \<longleftrightarrow> (\<exists>x. bmember x B \<and> y = f x)\<close>
  by transfer (force simp add: image_def)

lemma bCollect_eq_bempty_iff:
  \<open>bCollect p = bempty \<longleftrightarrow> (\<nexists>x. p x)\<close>
  by (metis Collect_empty_eq bCollect.rep_eq bempty.rep_eq set_bset_inject)


datatype runst = Running | Halted

datatype label = Env | Local act

codatatype 'a tree =
  Branch 'a runst \<open>(label \<times> 'a tree) set[(label \<times> 'a \<times> 'a comm) set]\<close>

corec treesem
  :: \<open>('l \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l::pre_perm_alg \<times> 's) comm \<Rightarrow>
      'l \<times> 's \<Rightarrow>
      ('l \<times> 's) tree\<close>
  where
  \<open>treesem F r c s =
    (case s of (hl, hs) \<Rightarrow>
      Branch s (if c = Skip then Halted else Running)
        (map_bset
          (\<lambda>(l, (hl', hs'), c'). (l, treesem F r c' (hl', hs')))
          (bCollect
            (\<lambda>(l, (hl', hs'), c').
              (\<exists>\<alpha>. l = Local \<alpha> \<and> ((hl, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl', hs'), c')) \<or>
              (\<exists>\<alpha> hf.
                F hf \<and>  hl ## hf \<and> hl' ## hf \<and> l = Local \<alpha> \<and>
                ((hl + hf, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl' + hf, hs'), c')) \<or>
              l = Env \<and> c' = c \<and> r hs hs'))))\<close>

coinductive treesafe
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('l \<times> 's \<Rightarrow> bool) \<Rightarrow> ('l \<times> 's) tree \<Rightarrow> bool\<close>
  where
    \<open>(runst = Halted \<longrightarrow> q (hl, hs)) \<Longrightarrow>
      (\<And>hl' hs' runst' B'.
        bmember (Local \<alpha>, Branch (hl', hs') runst' B') B \<Longrightarrow>
        \<alpha> \<noteq> Tau \<Longrightarrow>
        g hs hs') \<Longrightarrow>
      treesafe g q (Branch (hl, hs) runst B)\<close>



lemma treesem_first_state_eq[simp]:
  \<open>treesem F r c s1 = Branch s2 runst B \<Longrightarrow> s1 = s2\<close>
  by (subst (asm) treesem.code, simp split: prod.splits)

lemma treesem_runst_Skip[simp]:
  \<open>treesem F r c s1 = Branch s2 runst B \<Longrightarrow> c = Skip \<Longrightarrow> runst = Halted\<close>
  by (subst (asm) treesem.code, simp split: prod.splits)

lemma treesem_runst_nonSkip[simp]:
  \<open>treesem F r c s1 = Branch s2 runst B \<Longrightarrow> c \<noteq> Skip \<Longrightarrow> runst = Running\<close>
  by (subst (asm) treesem.code, simp split: prod.splits)


lemma treesafe_treesem_cases:
  \<open>treesafe g q (treesem F r c s) \<Longrightarrow>
    (\<And>hl hs \<alpha>.
      s = (hl, hs) \<Longrightarrow>
      ((\<forall>\<alpha> hl' hs' c'. \<not> opstep \<alpha> ((hl, hs), c) (Inl (hl', hs'), c')) \<Longrightarrow>
        (\<forall>\<alpha> hl' hs' c' hf.
          a ## hf \<longrightarrow>
          hl ## hf \<longrightarrow>
          F hf \<longrightarrow>
          \<not> opstep \<alpha> ((hl + hf, hs), c) (Inl (hl' + hf, hs'), c')) \<Longrightarrow>
        (\<forall>hs'. \<not> r hs hs') \<Longrightarrow>
        q (hl, hs)) \<Longrightarrow>
      (\<And>hl' hs' runst' B' c'.
          opstep \<alpha> ((hl, hs), c) (Inl (hl', hs'), c') \<Longrightarrow>
          treesem F r c' (hl', hs') = Branch (hl', hs') runst' B' \<Longrightarrow>
          \<alpha> \<noteq> act.Tau \<Longrightarrow>
          g hs hs') \<Longrightarrow>
      (\<And>hl' hs' runst' B' c' hf.
          F hf \<Longrightarrow>
          hl ## hf \<Longrightarrow>
          hl' ## hf \<Longrightarrow>
          opstep \<alpha> ((hl + hf, hs), c) (Inl (hl' + hf, hs'), c') \<Longrightarrow>
          treesem F r c' (hl', hs') = Branch (hl', hs') runst' B' \<Longrightarrow>
          \<alpha> \<noteq> act.Tau \<Longrightarrow>
          g hs hs') \<Longrightarrow>
      P) \<Longrightarrow>
    P\<close>
  apply (erule treesafe.cases)
  apply clarsimp
  apply (subst (asm)(3) treesem.code)
  apply (clarsimp simp add: bmember_bmap_iff bCollect_eq_bempty_iff
      all_conj_distrib split: prod.splits if_splits)
   apply (drule_tac y=\<alpha> in meta_spec2, drule meta_mp, rule refl)
   apply metis
  apply (drule_tac y=\<alpha> in meta_spec2, drule meta_mp, rule refl)
  apply (simp add: conj_disj_distribR ex_disj_distrib)
  oops

lemma treesafe_impl_safe:
  \<open>treesafe g q (treesem F r c s) \<Longrightarrow> safe n c (Inl s) r g q F\<close>
  apply (induct n arbitrary: s)
   apply force
  apply (erule treesafe_treesem_cases)
  apply clarsimp
  apply (rule safe_suc)
     apply (clarsimp simp add: opstep_iff safe_skip_iff)



     apply (subst (asm) (2) treesem.code)
     apply (clarsimp simp add: bCollect_eq_bempty_iff bmember_bmap_iff)
  sorry

end