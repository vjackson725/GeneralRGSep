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


section \<open> Alternate safe including forall steps property too \<close>

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
          ((hl,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl',hs'), c') \<longrightarrow>
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
            ((hl,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl',hs'), c') \<and>
            (\<alpha> = Tau \<longrightarrow> hl' = hl)))\<close>
  apply (subst safe_suc_iff)
  apply (rule conj_cong[OF refl])+
  apply (rule iffI)
   apply clarsimp
  oops

end