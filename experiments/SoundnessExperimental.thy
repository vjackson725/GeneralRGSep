theory SoundnessExperimental
  imports "../Soundness"
begin

lemma safe_suc_iff2:
  fixes hl :: \<open>'l::pre_perm_alg\<close>
    and hs :: 's
  assumes cancellative:
    \<open>\<forall>x y z::'l. x ## z \<longrightarrow> y ## z \<longrightarrow> x + z = y + z \<longrightarrow> x = y\<close>
  shows
    \<open>safe (Suc n) c (Inl (hl, hs)) r g q S F \<longleftrightarrow>
      (c = Skip \<longrightarrow> q (hl, hs)) \<and>
      S (hl, hs) \<and>
      (\<forall>hs'. r hs hs' \<longrightarrow> safe n c (Inl (hl, hs')) r g q S F) \<and>
      (\<forall>\<alpha> c' hl' hs'.
          ((hl,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl',hs'), c') \<longrightarrow>
          safe n c' (Inl (hl',hs')) r g q S F \<and>
          (\<alpha> \<noteq> Tau \<longrightarrow> g hs hs')) \<and>
      (\<forall>\<alpha> c' hlf hlhlf' hs' hl'.
          hl ## hlf \<longrightarrow>
           hl' ## hlf  \<longrightarrow>
          ((hl + hlf,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl' + hlf,hs'), c') \<longrightarrow>
          F (hlf, hs) \<longrightarrow>
          safe n c' (Inl (hl',hs')) r g q S F \<and>
          (\<alpha> \<noteq> Tau \<longrightarrow> g hs hs')) \<and>
      (\<forall>\<alpha> hlf hlhlf' hs' c'.
          F (hlf, hs) \<longrightarrow>
          hl ## hlf \<longrightarrow>
          ((hl + hlf,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hlhlf',hs'), c') \<longrightarrow>
          (\<exists>hl'.
            hl' ## hlf \<and>
            hlhlf' = hl' + hlf \<and>
            (\<alpha> = Tau \<longrightarrow> hl' = hl)))\<close>
  apply (simp add: safe_suc_iff)
  apply (rule conj_cong[OF refl])+
  apply (rule iffI)
   apply (rule conjI)
    apply clarsimp
    apply (metis cancellative)
   apply metis
  apply (metis cancellative)
  done

lemma safe_suc_iff3:
  fixes hl :: \<open>'l::pre_perm_alg\<close>
    and hs :: 's
  assumes cancellative:
    \<open>\<forall>x y z::'l. x ## z \<longrightarrow> y ## z \<longrightarrow> x + z = y + z \<longrightarrow> x = y\<close>
  shows
    \<open>safe (Suc n) c (Inl (hl, hs)) r g q S F \<longleftrightarrow>
      (c = Skip \<longrightarrow> q (hl, hs)) \<and>
      S (hl, hs) \<and>
      (\<forall>hs'. r hs hs' \<longrightarrow> safe n c (Inl (hl, hs')) r g q S F) \<and>
      (\<forall>\<alpha> c' hl' hs'.
          ((hl,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl',hs'), c') \<longrightarrow>
          safe n c' (Inl (hl',hs')) r g q S F \<and>
          (\<alpha> \<noteq> Tau \<longrightarrow> g hs hs')) \<and>
      (\<forall>\<alpha> c' hlf hlhlf' hs' hl'.
          hl ## hlf \<longrightarrow>
           hl' ## hlf  \<longrightarrow>
          ((hl + hlf,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl' + hlf,hs'), c') \<longrightarrow>
          ((\<exists>hl'2. hl'2 \<noteq> hl' \<and> hl'2 ## hlf \<and> hl' + hlf = hl'2 + hlf) \<longrightarrow>
            ((hl,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl',hs'), c')) \<longrightarrow>
          F (hlf, hs) \<longrightarrow>
          safe n c' (Inl (hl',hs')) r g q S F \<and>
          (\<alpha> \<noteq> Tau \<longrightarrow> g hs hs')) \<and>
      (\<forall>\<alpha> hlf hlhlf' hs' c'.
          F (hlf, hs) \<longrightarrow>
          hl ## hlf \<longrightarrow>
          ((hl + hlf,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hlhlf',hs'), c') \<longrightarrow>
          (\<exists>hl'.
            hl' ## hlf \<and>
            hlhlf' = hl' + hlf \<and>
            ((\<exists>hl'2. hl'2 \<noteq> hl' \<and> hl'2 ## hlf \<and> hl' + hlf = hl'2 + hlf) \<longrightarrow>
              ((hl,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl',hs'), c'))))\<close>
  apply (subst safe_suc_iff)
  apply (rule conj_cong[OF refl])+
  apply (rule iffI)
   apply (rule conjI)
    apply metis
   apply (metis cancellative)
  apply clarsimp
  apply (drule spec, drule mp, assumption, drule mp, assumption)
  apply (drule spec2, drule spec2, drule mp, assumption)
  apply clarsimp
  apply (erule opstep_act_cases)
   apply (metis Inl_inject cancellative fst_conv)
  apply (metis act.distinct(1))
  done

lemma safe_suc_iff3:
  fixes hl :: \<open>'l::pre_perm_alg\<close>
    and hs :: 's
  assumes cancellative:
    \<open>\<forall>x y z::'l. x ## z \<longrightarrow> y ## z \<longrightarrow> x + z = y + z \<longrightarrow> x = y\<close>
  shows
    \<open>safe (Suc n) c (Inl (hl, hs)) r g q S F \<longleftrightarrow>
      (c = Skip \<longrightarrow> q (hl, hs)) \<and>
      S (hl, hs) \<and>
      (\<forall>hs'. r hs hs' \<longrightarrow> safe n c (Inl (hl, hs')) r g q S F) \<and>
      (\<forall>\<alpha> c' hl' hs'.
          ((hl,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl',hs'), c') \<longrightarrow>
          safe n c' (Inl (hl',hs')) r g q S F \<and>
          (\<alpha> \<noteq> Tau \<longrightarrow> g hs hs')) \<and>
      (\<forall>\<alpha> c' hlf hlhlf' hs' hl'.
          hl ## hlf \<longrightarrow>
          hl' ## hlf  \<longrightarrow>
          ((hl + hlf,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl' + hlf,hs'), c') \<longrightarrow>
          F (hlf, hs) \<longrightarrow>
          ((\<exists>hl'. ((hl, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl', hs'), c')) \<longrightarrow>
            ((hl, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl', hs'), c')) \<longrightarrow>
          safe n c' (Inl (hl',hs')) r g q S F \<and>
          (\<alpha> \<noteq> Tau \<longrightarrow> g hs hs')) \<and>
      (\<forall>\<alpha> hlf hlhlf' hs' c'.
          F (hlf, hs) \<longrightarrow>
          hl ## hlf \<longrightarrow>
          ((hl + hlf,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hlhlf',hs'), c') \<longrightarrow>
          (\<exists>hl'.
            hl' ## hlf \<and>
            hlhlf' = hl' + hlf \<and>
            ((\<exists>hl'. ((hl, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl', hs'), c')) \<longrightarrow>
              ((hl, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl', hs'), c'))))\<close>
  apply (subst safe_suc_iff)
  apply (rule conj_cong[OF refl])+
  apply (rule iffI)
   apply (rule conjI)
    apply (metis cancellative)
   apply clarsimp

  oops


end