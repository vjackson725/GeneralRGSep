theory SoundnessExperimental
  imports "../Soundness"
begin

section \<open> Alternate safe with restricted rely condition \<close>

subsubsection \<open> Safe alternates \<close>

lemma safe_suc_iff_frame_alt:
  \<open>safe (Suc n) c (Inl s) r g q S F \<Longrightarrow>
    (c = Skip \<longrightarrow> q s) \<and>
    S s \<and>
    \<comment> \<open> note the assumption here \<close>
    ((\<exists>hlf. F (hlf, snd s) \<and> fst s ## hlf) \<longrightarrow>
      (\<forall>hs'. r (snd s) hs' \<longrightarrow> safe n c (Inl (fst s, hs')) r g q S F)) \<and>
    (\<forall>hlf.
      F (hlf, snd s) \<longrightarrow>
      fst s ## hlf \<longrightarrow>
      (\<forall>\<alpha> z' c'.
        ((fst s + hlf, snd s), c) \<midarrow>\<alpha>\<rightarrow> (z', c') \<longrightarrow>
        (\<exists>hlhlf' hs'.
          z' = Inl (hlhlf',hs') \<and>
          (\<alpha> \<noteq> Tau \<longrightarrow> g (snd s) hs') \<and>
          (\<exists>hl'.
            hl' ## hlf \<and>
            hlhlf' = hl' + hlf \<and>
            (\<alpha> = Tau \<longrightarrow> hl' = fst s) \<and>
            safe n c' (Inl (hl',hs')) r g q S F))))\<close>
  by (simp add: safe_suc_iff)
  \<comment> \<open> this is obviously only weaker than the original \<close>

\<comment> \<open> this is probably the one we actually want \<close>
lemma safe_iff_frame_alt2:
    \<open>(c = Skip \<longrightarrow> q s) \<and>
      S s \<and>
      \<comment> \<open> note the additional test \<close>
      (\<exists>hlf. F (hlf, snd s) \<and> fst s ## hlf) \<and>
      (0 < n \<longrightarrow>
        (\<forall>hs'. r (snd s) hs' \<longrightarrow> safe (n-1) c (Inl (fst s, hs')) r g q S F) \<and>
        (\<forall>hlf.
          F (hlf, snd s) \<longrightarrow>
          fst s ## hlf \<longrightarrow>
          (\<forall>\<alpha> z' c'.
            ((fst s + hlf, snd s), c) \<midarrow>\<alpha>\<rightarrow> (z', c') \<longrightarrow>
            (\<exists>hlhlf' hs'.
              z' = Inl (hlhlf',hs') \<and>
              (\<alpha> \<noteq> Tau \<longrightarrow> g (snd s) hs') \<and>
              (\<exists>hl'.
                hl' ## hlf \<and>
                hlhlf' = hl' + hlf \<and>
                (\<alpha> = Tau \<longrightarrow> hl' = fst s) \<and>
                safe (n-1) c' (Inl (hl',hs')) r g q S F))))) \<Longrightarrow>
    safe n c (Inl s) r g q S F\<close>
  apply (induct n arbitrary: s r)
   apply force
  apply (simp add: safe_suc_iff)
  done


section \<open> Safe2 \<close>

definition safe2 where
  \<open>safe2 n c (s :: 'l::pre_perm_alg \<times> 's + unit) r g q S F \<equiv>
    \<exists>hl hs. s = Inl (hl, hs) \<and>
      (if n > 0 then
        (c = Skip \<longrightarrow> q (hl, hs)) \<and>
        S (hl, hs) \<and>
        (\<forall>\<alpha> flc fl z' c'.
            F (flc, hs) \<longrightarrow>
            hl ## flc \<longrightarrow>
            fl \<preceq> flc \<longrightarrow> 
            ((hl + fl, hs), c) \<midarrow>\<alpha>\<rightarrow> (z', c') \<longrightarrow>
            (\<exists>hl' hlfl' hs'.
              z' = Inl (hlfl',hs') \<and>
              hl' ## fl \<and>
              hlfl' = hl' + fl \<and>
              (\<alpha> = Tau \<longrightarrow> hl' = hl))) \<and>
        (\<forall>hs'. r hs hs' \<longrightarrow> safe (n-1) c (Inl (hl, hs')) r g q S F) \<and>
        (\<forall>\<alpha> c' hlf hs' hl'.
            F (hlf, hs) \<longrightarrow>
            hl ## hlf \<longrightarrow>
            hl' ## hlf  \<longrightarrow>
            ((hl + hlf,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl' + hlf,hs'), c') \<longrightarrow>
            safe (n-1) c' (Inl (hl',hs')) r g q S F \<and>
            (\<alpha> \<noteq> Tau \<longrightarrow> g hs hs'))
      else True)\<close>

lemmas safe2_nil_iff[simp] = safe2_def[of 0, simplified]
lemmas safe2_suc_iff = safe2_def[of \<open>Suc n\<close> for n, simplified]

lemma cancellative_safe_iff_safe2:
  fixes z :: \<open>'l::pre_perm_alg \<times> 's + unit\<close>
  assumes \<open>\<forall>fl fs. F (fl, fs) \<longrightarrow> cancellative fl\<close>
  shows \<open>safe n c z r g q S F \<longleftrightarrow> safe2 n c z r g q S F\<close>
  apply (induct n arbitrary: c z)
   apply force
  apply (clarsimp simp add: safe2_suc_iff safe_suc_iff split: if_splits)
  apply (rule iffI)
    (* \<rightarrow> *)
   apply clarsimp
  subgoal sorry
      (*
   apply (intro conjI)
    apply blast
   apply clarsimp
   apply (drule spec, drule mp, assumption, drule spec2, drule spec, drule mp, assumption)
   apply clarsimp
    apply (metis assms cancellative_def)
*)
      (* \<leftarrow> *)
  apply clarsimp
  apply (metis resource_preordering.refl)
  done


subsection \<open> Safety (2) of frame \<close>

lemma sepimp_conj_mp:
  \<open>p (y, z) \<Longrightarrow> (p \<midarrow>\<^emph>\<^sub>\<and> q) (x, z) \<Longrightarrow> x ## y \<Longrightarrow> q (x + y, z)\<close>
  by (simp add: disjoint_sym_iff sepimp_conj_apply)

lemma safe_frame':
  \<open>safe2 n c z r g q S F \<Longrightarrow>
    z = Inl (hl, hs) \<Longrightarrow>
    hl ## hlf \<Longrightarrow>
    sswa (r \<squnion> g) f (hlf, hs) \<Longrightarrow>
    safe2 n c (Inl (hl + hlf, hs)) r g (q \<^emph>\<and> sswa (r \<squnion> g) f) (S \<^emph>\<and> sswa (r \<squnion> g) f) (sswa (r \<squnion> g) f \<midarrow>\<^emph>\<^sub>\<and> F)\<close>
proof (induct n arbitrary: c z hl hs hlf)
  case (0 n c z hlx hsx)
  then show ?case by simp
next
  case (Suc n c z hlx hsx flx)

  obtain hl hs where ih:
    \<open>z = Inl (hl, hs)\<close>
    \<open>c = Skip \<longrightarrow> q (hl, hs)\<close>
    \<open>S (hl, hs)\<close>
    \<open>\<forall>flc fl.
      F (flc, hs) \<longrightarrow>
      hl ## flc \<longrightarrow>
      fl \<preceq> flc \<longrightarrow>
      (\<forall>\<alpha> z'.
        (\<exists>c'. ((hl + fl, hs), c) \<midarrow>\<alpha>\<rightarrow> (z', c')) \<longrightarrow>
        (\<exists>hl' hlfl'.
          (\<exists>hs'. z' = Inl (hlfl', hs')) \<and>
          hl' ## fl \<and> hlfl' = hl' + fl \<and> (\<alpha> = Tau \<longrightarrow> hl' = hl)))\<close>
    \<open>\<forall>hs'. r hs hs' \<longrightarrow> safe n c (Inl (hl, hs')) r g q S F\<close>
    \<open>\<forall>hlf. F (hlf, hs) \<longrightarrow>
            hl ## hlf \<longrightarrow>
            (\<forall>hl'. hl' ## hlf \<longrightarrow>
                   (\<forall>\<alpha> c' hs'.
                       ((hl + hlf, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl' + hlf, hs'), c') \<longrightarrow>
                       safe n c' (Inl (hl', hs')) r g q S F \<and> (\<alpha> = Vis () \<longrightarrow> g hs hs')))\<close>
    using Suc.prems(1)
    by (clarsimp simp add: safe2_suc_iff)

  have frame_condition:
    \<open>\<And>fly fl \<alpha> z' c'.
      (sswa (r \<squnion> g) f \<midarrow>\<^emph>\<^sub>\<and> F) (fly, hsx) \<Longrightarrow>
      fl \<preceq> flx + fly \<Longrightarrow>
      hlx + flx ## fly \<Longrightarrow>
      ((hlx + fl, hsx), c) \<midarrow>\<alpha>\<rightarrow> (z', c') \<Longrightarrow>
      (\<exists>hl'. (\<exists>hs'. z' = Inl (hl' + fl, hs')) \<and> hl' ## fl \<and> (\<alpha> = Tau \<longrightarrow> hl' = hlx))\<close>
    using Suc.prems(2-) ih(1,4)
    apply (clarsimp simp add: safe2_suc_iff simp del: sup_apply)
    apply (frule(1) sepimp_conj_mp[of \<open>sswa (r \<squnion> g) f\<close> _ _ F])
     apply (metis disjoint_add_leftR disjoint_sym)
    apply (frule(1) disjoint_add_swap_lr2)
    apply (drule spec, drule mp, assumption, drule mp, assumption)
    apply (subgoal_tac \<open>fly + flx = flx + fly\<close>)
     prefer 2
     apply (metis disjoint_add_leftR partial_add_commute)
    apply (subgoal_tac \<open>hlx + (flx + fly) = hlx + flx + fly\<close>)
     prefer 2
     apply (metis partial_add_assoc2)
    apply (drule_tac x=fl in spec, drule mp, presburger)
    apply force
    done

  show ?case
    using Suc.prems(2-)
    apply (clarsimp simp add: safe2_suc_iff simp del: sup_apply)
    apply (intro conjI)
      (* subgoal: skip *)
        apply (metis ih(1,2) sepconj_conj_apply sum.inject(1))
      (* subgoal: stateset *)
       apply (metis ih(1,3) sepconj_conj_apply sum.inject(1))
      (* subgoal: frame condition *)
      apply (clarsimp simp del: sup_apply)
      apply (subgoal_tac \<open>hlx + (flx + fl) = hlx + flx + fl\<close>)
       prefer 2
       apply (metis disjoint_add_leftL disjoint_add_leftR disjoint_preservation2 partial_add_assoc)
      apply (drule_tac fl=\<open>flx + fl\<close> in frame_condition)
         apply (metis disjoint_add_leftR disjoint_preservation2 sepadd_left_mono)
        apply blast
       apply force
      apply (metis (no_types, opaque_lifting) disjoint_add_leftR disjoint_add_swap_rl
        disjoint_preservation2 partial_add_assoc3)
      (* subgoal: rely step *)
     apply (cut_tac ih(1,5))
     apply (clarsimp simp del: sup_apply)
     apply (metis safe_frame' sswa_step sup2CI)
      (* subgoal: framed opstep *)
    apply (clarsimp simp add: partial_add_assoc2[of hl hlf] simp del: sup_apply)
    apply (cut_tac ih(1,6))
    apply (clarsimp simp del: sup_apply)
    apply (frule(1) sepimp_conj_mp[of \<open>sswa (r \<squnion> g) f\<close> _ _ F])
     apply (metis disjoint_add_leftR disjoint_sym)
    apply (drule spec, drule mp, assumption)
    apply (drule mp[of \<open>_ ## _\<close>], metis disjoint_add_swap_lr2)
    apply (drule_tac x=hl' in spec, drule mp[of \<open>_ ## _\<close>])
    sorry
qed


end