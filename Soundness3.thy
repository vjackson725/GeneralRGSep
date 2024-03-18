theory Soundness3
  imports RGSep
begin

section \<open> Operational Semantics \<close>

subsection \<open> Actions \<close>

datatype act = Tau | Local

lemma act_not_eq_iff[simp]:
  \<open>a \<noteq> Tau \<longleftrightarrow> a = Local\<close>
  \<open>a \<noteq> Local \<longleftrightarrow> a = Tau\<close>
  by (meson act.distinct act.exhaust)+

subsection \<open> Operational semantics steps \<close>

inductive opstep :: \<open>act \<Rightarrow> ('h::perm_alg) \<times> 'h comm \<Rightarrow> ('h \<times> 'h comm) \<Rightarrow> bool\<close> where
  seq_left[intro!]: \<open>opstep a (h, c1) (h', c1') \<Longrightarrow> opstep a (h, c1 ;; c2) (h', c1' ;; c2)\<close>
| seq_right[intro!]: \<open>opstep Tau (h, Skip ;; c2) (h, c2)\<close>
| ndet_tau_left[intro]:  \<open>opstep Tau (h, c1) (h', c1') \<Longrightarrow> opstep Tau (h, c1 \<^bold>+ c2) (h', c1' \<^bold>+ c2)\<close>
| ndet_tau_right[intro]: \<open>opstep Tau (h, c2) (h', c2') \<Longrightarrow> opstep Tau (h, c1 \<^bold>+ c2) (h', c1 \<^bold>+ c2')\<close>
| ndet_skip_left[intro!]:  \<open>opstep Tau (h, Skip \<^bold>+ c2) (h, c2)\<close>
| ndet_skip_right[intro!]: \<open>opstep Tau (h, c1 \<^bold>+ Skip) (h, c1)\<close>
| ndet_local_left[intro]:  \<open>opstep Local (h, c1) s' \<Longrightarrow> opstep Local (h, c1 \<^bold>+ c2) s'\<close>
| ndet_local_right[intro]: \<open>opstep Local (h, c2) s' \<Longrightarrow> opstep Local (h, c1 \<^bold>+ c2) s'\<close>
| par_left[intro]:  \<open>opstep a (h, s) (h', s') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| par_right[intro]: \<open>opstep a (h, t) (h', t') \<Longrightarrow> opstep a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| par_skip[intro!]:  \<open>opstep Tau (h, Skip \<parallel> Skip) (h, Skip)\<close>
| iter_skip[intro]: \<open>opstep Tau (h, c\<^sup>\<star>) (h, Skip)\<close>
  \<comment> \<open> TODO: not quite right... c has to not be able to take a move? \<close>
| iter_step[intro]: \<open>opstep Tau (h, c\<^sup>\<star>) (h, c ;; c\<^sup>\<star>)\<close>
| atomic[intro!]: \<open>a = Local \<Longrightarrow> snd s' = Skip \<Longrightarrow> b h (fst s') \<Longrightarrow> opstep a (h, Atomic b) s'\<close>

inductive_cases opstep_tauE[elim]: \<open>opstep Tau s s'\<close>
inductive_cases opstep_localE[elim]: \<open>opstep Local s s'\<close>

inductive_cases opstep_skipE[elim!]: \<open>opstep a (h, Skip) s'\<close>
inductive_cases opstep_seqE[elim]: \<open>opstep a (h, c1 ;; c2) s'\<close>
inductive_cases opstep_ndetE[elim]: \<open>opstep a (h, c1 \<^bold>+ c2) s'\<close>
inductive_cases opstep_parE[elim]: \<open>opstep a (h, c1 \<parallel> c2) s'\<close>
inductive_cases opstep_iterE[elim]: \<open>opstep a (h, c\<^sup>\<star>) s'\<close>
inductive_cases opstep_atomicE[elim!]: \<open>opstep a (h, Atomic b) s'\<close>

paragraph \<open> Pretty operational semantics \<close>

abbreviation(input) pretty_opstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>a\<rightarrow> ht \<equiv> opstep a hs ht\<close>

subsection \<open> Lemmas about opstep \<close>

named_theorems opstep_iff

lemma opstep_iff_standard[opstep_iff]:
  \<open>opstep a (h, Skip) s' \<longleftrightarrow> False\<close>
  \<open>opstep a (h, c1 ;; c2) s' \<longleftrightarrow>
    a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
    (\<exists>h' c1'. opstep a (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
  \<open>opstep a (h, c1 \<^bold>+ c2) s' \<longleftrightarrow>
    a = Local \<and> opstep Local (h, c1) s' \<or>
    a = Local \<and> opstep Local (h, c2) s' \<or>
    a = Tau \<and> (\<exists>h' c1'. s' = (h', c1' \<^bold>+ c2) \<and> opstep Tau (h, c1) (h', c1')) \<or>
    a = Tau \<and> (\<exists>h' c2'. s' = (h', c1 \<^bold>+ c2') \<and> opstep Tau (h, c2) (h', c2')) \<or>
    a = Tau \<and> c1 = Skip \<and> s' = (h, c2) \<or>
    a = Tau \<and> c2 = Skip \<and> s' = (h, c1)\<close>
  \<open>opstep a (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    a = Tau \<and> c1 = Skip \<and> c2 = Skip \<and> s' = (h, Skip) \<or>
    (\<exists>h' c1'. opstep a (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2)) \<or>
    (\<exists>h' c2'. opstep a (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2'))\<close>
  \<open>opstep a (h, c\<^sup>\<star>) s' \<longleftrightarrow>
    a = Tau \<and> s' = (h, Skip) \<or>
    a = Tau \<and> s' = (h, c ;; c\<^sup>\<star>)\<close>
  \<open>opstep a (h, Atomic b) s' \<longleftrightarrow>
    a = Local \<and> snd s' = Skip \<and> b h (fst s')\<close>
       apply force
      apply force
     apply (rule iffI, (erule opstep_ndetE; force), force)
    apply (rule iffI, (erule opstep_parE; force), force)
   apply (rule iffI, (erule opstep_iterE; force), force)
  apply (rule iffI, (erule opstep_atomicE; force), force)
  done

lemma opstep_tau_preserves_heap:
  assumes \<open>s \<midarrow>Tau\<rightarrow> s'\<close>
  shows \<open>fst s' = fst s\<close>
proof -
  { fix a
    have \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> a = Tau \<Longrightarrow> fst s' = fst s\<close>
      by (induct rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms by force
qed

lemma opstep_act_cases:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow>
    (a = Tau \<Longrightarrow> s \<midarrow>Tau\<rightarrow> s' \<Longrightarrow> fst s' = fst s \<Longrightarrow> P) \<Longrightarrow>
    (a = Local \<Longrightarrow> s \<midarrow>Local\<rightarrow> s' \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  by (metis (full_types) act.exhaust opstep_tau_preserves_heap)

lemma opstep_to_ndet_originally_ndet_subexpr:
  \<open>opstep a s s' \<Longrightarrow> snd s' = c1' \<^bold>+ c2' \<Longrightarrow>
    (\<exists>c1. c1 \<^bold>+ c2' \<le> snd s) \<or> (\<exists>c2. c1' \<^bold>+ c2 \<le> snd s)\<close>
  by (induct arbitrary: c1' c2' rule: opstep.inducts) force+

lemma opstep_step_to_under_left_ndet_impossible:
  \<open>opstep a s s' \<Longrightarrow> c1' \<^bold>+ c2' \<le> snd s' \<Longrightarrow> snd s \<le> c1' \<Longrightarrow> False\<close>
  apply (induct arbitrary: c1' c2' rule: opstep.inducts; clarsimp)
            apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(1,2))
           apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(2))
          apply (metis order.refl less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(3,4))
         apply (metis order.refl less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(3,4))
        apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(4))
       apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(3))
      apply (metis less_eq_comm_subexprsD(3))
     apply (metis less_eq_comm_subexprsD(4))
    apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(5,6))
   apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(5,6))
  apply (metis less_eq_comm_no_constructorsD(3) less_eq_comm_subexprsD(7))
  done

lemma opstep_step_to_left_ndet_impossible:
  \<open>opstep a (h, c1) (h', c1 \<^bold>+ c2) \<Longrightarrow> False\<close>
  by (metis order.refl opstep_step_to_under_left_ndet_impossible snd_conv)

lemma opstep_step_to_under_right_ndet_impossible:
  \<open>opstep a s s' \<Longrightarrow> c1' \<^bold>+ c2' \<le> snd s' \<Longrightarrow> snd s \<le> c2' \<Longrightarrow> False\<close>
  apply (induct arbitrary: c1' c2' rule: opstep.inducts; clarsimp)
            apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(1,2))
           apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(2))
          apply (metis order.refl less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(3,4))
         apply (metis order.refl less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(3,4))
        apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(4))
       apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(3))
      apply (metis less_eq_comm_subexprsD(3))
     apply (metis less_eq_comm_subexprsD(4))
    apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(5,6))
   apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(5,6))
  apply (metis less_eq_comm_no_constructorsD(4) less_eq_comm_subexprsD(7))
  done

lemma opstep_step_to_right_ndet_impossible:
  \<open>opstep a (h, c2) (h', c1 \<^bold>+ c2) \<Longrightarrow> False\<close>
  by (metis order.refl opstep_step_to_under_right_ndet_impossible snd_conv)

lemma opstep_always_changes_comm:
  \<open>opstep a s s' \<Longrightarrow> snd s' \<noteq> snd s\<close>
  by (induct rule: opstep.inducts)
    (force dest: opstep_step_to_left_ndet_impossible opstep_step_to_right_ndet_impossible)+

lemma all_atom_comm_opstep:
  assumes
    \<open>opstep a (h, c) (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows
    \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    assume \<open>opstep a s s'\<close>
      and \<open>all_atom_comm p (snd s)\<close>
    then have \<open>all_atom_comm p (snd s')\<close>
      by (induct rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms
    by force
qed

lemmas all_atom_comm_opstepD =
  all_atom_comm_opstep[rotated]

subsubsection \<open> Frame properties \<close>

definition
  \<open>local_frame_safe \<ff> \<equiv> \<lambda>r.
    \<forall>l s l' s' lf lf'.
      r (l,s) (l',s') \<longrightarrow> \<ff> lf lf' \<longrightarrow> l ## lf \<longrightarrow> l' ## lf' \<longrightarrow> r (l + lf,s) (l' + lf', s')\<close>

lemma local_frame_safe_framerel_antimonoD[dest]:
  \<open>\<ff>1 \<le> \<ff>2 \<Longrightarrow> local_frame_safe \<ff>2 r \<Longrightarrow> local_frame_safe \<ff>1 r\<close>
  by (force simp add: local_frame_safe_def)

lemma opstep_local_frame':
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow>
    weak_framed_subresource_rel f (fst (fst s)) (fst (fst s')) lf lf' \<Longrightarrow>
    all_atom_comm (local_frame_safe (rel_lift f)) (snd s) \<Longrightarrow>
    ((lf, snd (fst s)), snd s) \<midarrow>a\<rightarrow> ((lf', snd (fst s')), snd s')\<close>
  apply (induct rule: opstep.inducts)
               apply (force simp add: opstep_iff ndet_local_left ndet_local_right)+
  apply (force simp add: framed_subresource_rel_def local_frame_safe_def)
  done

lemma opstep_local_frame:
  \<open>((l, s), c) \<midarrow>a\<rightarrow> ((l', s'), c') \<Longrightarrow>
    weak_framed_subresource_rel f l l' lf lf' \<Longrightarrow>
    all_atom_comm (local_frame_safe (rel_lift f)) c \<Longrightarrow>
    ((lf, s), c) \<midarrow>a\<rightarrow> ((lf', s'), c')\<close>
  by (metis fst_conv opstep_local_frame' snd_conv)

lemma opstep_local_frame2:
  \<open>((l, s), c) \<midarrow>a\<rightarrow> ((l', s'), c') \<Longrightarrow>
    framed_subresource_rel f l l' lf lf' \<Longrightarrow>
    all_atom_comm (local_frame_safe (rel_lift f)) c \<Longrightarrow>
    ((lf, s), c) \<midarrow>a\<rightarrow> ((lf', s'), c')\<close>
  using opstep_local_frame by blast


lemma opstep_sameheap_frameD:
  assumes
    \<open>s \<midarrow>a\<rightarrow> s'\<close>
    \<open>fst s' = fst s\<close>
    \<open>fst s ## hf\<close>
    \<open>all_atom_comm (frame_pred_closed ((=) hf)) (snd s)\<close>
  shows
    \<open>(fst s + hf, snd s) \<midarrow>a\<rightarrow> (fst s' + hf, snd s')\<close>
  using assms
  by (induct rule: opstep.induct)
    (force simp add: frame_pred_safe_def atomic frame_pred_closed_def)+

lemma opstep_sameheap_frame:
  assumes
    \<open>(h, c) \<midarrow>a\<rightarrow> (h, c')\<close>
    \<open>h ## hf\<close>
    \<open>all_atom_comm (frame_pred_closed ((=) hf)) c\<close>
  shows
    \<open>(h + hf, c) \<midarrow>a\<rightarrow> (h + hf, c')\<close>
  using assms opstep_sameheap_frameD
  by fastforce

lemma opstep_frame_closedD:
  assumes
    \<open>s \<midarrow>a\<rightarrow> s'\<close>
    \<open>all_atom_comm (frame_pred_closed ((=) hf)) (snd s)\<close>
    \<open>fst s ## hf\<close>
    \<open>fst s' ## hf\<close>
  shows
    \<open>(fst s + hf, snd s) \<midarrow>a\<rightarrow> (fst s' + hf, snd s')\<close>
  using assms
  by (induct rule: opstep.induct)
    (force simp add: frame_pred_closed_def)+

lemma opstep_frame_closed:
  assumes
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
    \<open>all_atom_comm (frame_pred_closed ((=) hf)) c\<close>
    \<open>h ## hf\<close>
    \<open>h' ## hf\<close>
  shows
    \<open>(h + hf, c) \<midarrow>a\<rightarrow> (h' + hf, c')\<close>
  using assms opstep_frame_closedD
  by fastforce

lemma opstep_frameD:
  assumes
    \<open>s \<midarrow>a\<rightarrow> s'\<close>
    \<open>all_atom_comm (frame_pred_safe (rel_lift ((=) hf))) (snd s)\<close>
    \<open>fst s ## hf\<close>
    \<open>fst s' ## hf\<close>
  shows
    \<open>(fst s + hf, snd s) \<midarrow>a\<rightarrow> (fst s' + hf, snd s')\<close>
  using assms
  by (induct rule: opstep.induct)
    (force simp add: frame_pred_safe_def)+

lemma opstep_frame:
  assumes
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
    \<open>all_atom_comm (frame_pred_safe (rel_lift ((=) hf))) c\<close>
    \<open>h ## hf\<close>
    \<open>h' ## hf\<close>
  shows
    \<open>(h + hf, c) \<midarrow>a\<rightarrow> (h' + hf, c')\<close>
  using assms opstep_frameD
  by fastforce

lemma opstep_frame_pred_extendsD:
  assumes
    \<open>s1 \<midarrow>a\<rightarrow> s2\<close>
    \<open>all_atom_comm (frame_pred_extends f) (snd s1)\<close>
    \<open>fst s1 ## hf\<close>
    \<open>f hf\<close>
  shows
    \<open>\<exists>hf'. f hf' \<and> fst s2 ## hf' \<and> (fst s1 + hf, snd s1) \<midarrow>a\<rightarrow> (fst s2 + hf', snd s2)\<close>
  using assms
  by (induct arbitrary: hf rule: opstep.inducts)
    (force simp add: frame_pred_extends_def)+

lemma opstep_frame_pred_extends:
  assumes
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
    \<open>all_atom_comm (frame_pred_extends f) c\<close>
    \<open>h ## hf\<close>
    \<open>f hf\<close>
  shows
    \<open>\<exists>hf'. f hf' \<and> h' ## hf' \<and> (h + hf, c) \<midarrow>a\<rightarrow> (h' + hf', c')\<close>
  using assms
  by (force dest: opstep_frame_pred_extendsD)


lemma opstep_frame_pred_maintainsD:
  assumes
    \<open>s1 \<midarrow>a\<rightarrow> s2\<close>
    \<open>all_atom_comm (frame_pred_maintains f) (snd s1)\<close>
    \<open>fst s1 ## hf\<close>
    \<open>f hf\<close>
  shows
    \<open>fst s2 ## hf \<and> (fst s1 + hf, snd s1) \<midarrow>a\<rightarrow> (fst s2 + hf, snd s2)\<close>
  using assms
  by (induct arbitrary: hf rule: opstep.inducts)
    (force simp add: frame_pred_maintains_def opstep_iff)+

lemma opstep_frame_pred_maintains:
  assumes
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
    \<open>all_atom_comm (frame_pred_maintains f) c\<close>
    \<open>h ## hf\<close>
    \<open>f hf\<close>
  shows
    \<open>(h + hf, c) \<midarrow>a\<rightarrow> (h' + hf, c')\<close>
  using assms opstep_frame_pred_maintainsD
  by fastforce

lemma opstep_frame_pred_maintains2:
  assumes
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
    \<open>all_atom_comm (frame_pred_maintains f) c\<close>
    \<open>h ## hf\<close>
    \<open>f hf\<close>
  shows
    \<open>h' ## hf\<close>
  using assms opstep_frame_pred_maintainsD
  by fastforce

subsubsection \<open> Opstep Unframe \<close>

lemma opstep_unframe':
  fixes s s' :: \<open>('a::cancel_perm_alg) \<times> 'a comm\<close>
  assumes
    \<open>s \<midarrow>a\<rightarrow> s'\<close>
    \<open>s = (h + hf, c)\<close>
    \<open>s' = (h' + hf, c')\<close>
    \<open>all_atom_comm (unframe_safe (rel_lift ((=) hf))) c\<close>
    \<open>h ## hf\<close>
    \<open>h' ## hf\<close>
  shows
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
  using assms
  apply -
  apply (induct arbitrary: h h' c c' hf rule: opstep.induct)
                apply (simp add: opstep_iff; fail)+ (* slow *)
  apply (simp add: opstep_iff unframe_safeD)
  done

lemma opstep_unframe_right:
  fixes h :: \<open>'a::cancel_perm_alg\<close>
  assumes
    \<open>(h + hf, c) \<midarrow>a\<rightarrow> (h' + hf, c')\<close>
    \<open>all_atom_comm (unframe_safe (rel_lift ((=) hf))) c\<close>
    \<open>h ## hf\<close>
    \<open>h' ## hf\<close>
  shows
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
  using assms opstep_unframe'
  by blast

lemma opstep_unframe_left:
  fixes h :: \<open>'a::cancel_perm_alg\<close>
  assumes
    \<open>(hf + h, c) \<midarrow>a\<rightarrow> (hf + h', c')\<close>
    \<open>all_atom_comm (unframe_safe (rel_lift ((=) hf))) c\<close>
    \<open>hf ## h\<close>
    \<open>hf ## h'\<close>
  shows
    \<open>(h, c) \<midarrow>a\<rightarrow> (h', c')\<close>
  using assms opstep_unframe'
  by (metis disjoint_sym_iff partial_add_commute)


subsubsection \<open> adding parallel \<close>

lemma opstep_parallel_leftD:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> (fst s, snd s \<parallel> cy) \<midarrow>a\<rightarrow> (fst s', snd s' \<parallel> cy)\<close>
  by (simp add: par_left)

lemma opstep_parallel_rightD:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> (fst s, cx \<parallel> snd s) \<midarrow>a\<rightarrow> (fst s', cx \<parallel> snd s')\<close>
  by (simp add: par_right)


subsubsection \<open> iteraction with all_atom_comm \<close>

lemma opstep_preserves_all_atom_comm:
  assumes
    \<open>opstep a (h, c) (h', c')\<close>
    \<open>all_atom_comm p c\<close>
  shows \<open>all_atom_comm p c'\<close>
proof -
  { fix s s'
    have \<open>opstep a s s' \<Longrightarrow> all_atom_comm p (snd s) \<Longrightarrow> all_atom_comm p (snd s')\<close>
      by (induct arbitrary: h' rule: opstep.inducts) force+
  }
  then show ?thesis
    using assms
    by force
qed

lemmas rev_opstep_preserves_all_atom_comm = opstep_preserves_all_atom_comm[rotated]


subsection \<open> Operational Semantics \<close>

inductive opsem
  :: \<open>act list \<Rightarrow> ('a::perm_alg) \<times> 'a comm \<Rightarrow> 'a \<times> 'a comm \<Rightarrow> bool\<close>
  where
  base[intro!]: \<open>opsem [] s s\<close>
| step[intro!]: \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> opsem as s' s'' \<Longrightarrow> opsem (a # as) s s''\<close>

inductive_cases opsem_NilE[elim!]: \<open>opsem [] s s'\<close>
inductive_cases opsem_ConsE[elim!]: \<open>opsem (a # as) s s'\<close>

lemma opsem_iff[simp]:
  \<open>opsem [] s s' \<longleftrightarrow> s' = s\<close>
  \<open>opsem (a # as) s s'' \<longleftrightarrow> (\<exists>s'. (s \<midarrow>a\<rightarrow> s') \<and> opsem as s' s'')\<close>
  by force+


(*
paragraph \<open> pretty opsem \<close>

abbreviation(input) pretty_opsem :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sup>\<star> _\<close> [60,0,60] 60) where
  \<open>hc \<midarrow>as\<rightarrow>\<^sup>\<star> hc' \<equiv> opsem as hc hc'\<close>

subsection \<open> Theorems about the operational semantics \<close>

paragraph \<open> Reverse-cons transitive closure rules \<close>

lemma opsem_step_rev:
  \<open>opsem as s s' \<Longrightarrow> s' \<midarrow>a\<rightarrow> s'' \<Longrightarrow> opsem (as @ [a]) s s''\<close>
  apply (induct rule: opsem.induct)
   apply (metis append_self_conv2 opsem.simps)
  apply force
  done

lemma opsem_step_revE:
  \<open>opsem (as @ [a]) s s'' \<Longrightarrow> (\<And>s'. opsem as s s' \<Longrightarrow> opstep a s' s'' \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (induct as arbitrary: a s s'')
    (simp, blast)+

lemma opsem_rev_cons_iff[simp]:
  \<open>opsem (as @ [a]) s s'' \<longleftrightarrow> (\<exists>s'. opsem as s s' \<and> (s' \<midarrow>a\<rightarrow> s''))\<close>
  by (meson opsem_step_rev opsem_step_revE)

lemma opsem_rev_induct[consumes 1, case_names Nil Snoc]:
  \<open>opsem as s s' \<Longrightarrow>
    (\<And>r s. P r [] s s) \<Longrightarrow>
    (\<And>s r a s' as s''.
      opsem as s s' \<Longrightarrow>
      opstep a s' s'' \<Longrightarrow>
      P r as s s' \<Longrightarrow>
      P r (as @ [a]) s s'') \<Longrightarrow>
    P r as s s'\<close>
  by (induct as arbitrary: s s' rule: rev_induct) force+

lemma opsem_stepI:
  \<open>s \<midarrow>a\<rightarrow> s' \<Longrightarrow> s \<midarrow>[a]\<rightarrow>\<^sup>\<star> s'\<close>
  by blast

lemma opsem_trans:
  \<open>s \<midarrow>as1\<rightarrow>\<^sup>\<star> s' \<Longrightarrow> s' \<midarrow>as2\<rightarrow>\<^sup>\<star> s'' \<Longrightarrow> s \<midarrow>as1 @ as2\<rightarrow>\<^sup>\<star> s''\<close>
  by (induct arbitrary: as2 s'' rule: opsem.induct)
    force+

lemma skipped_opsem_only_env:
  \<open>s \<midarrow>as\<rightarrow>\<^sup>\<star> s' \<Longrightarrow> snd s = Skip \<Longrightarrow> as = []\<close>
  by (induct rule: opsem.induct)
    (force elim: opstep.cases)+

inductive opstep_trancl :: \<open>act list \<Rightarrow> ('h::perm_alg) \<times> 'h comm \<Rightarrow> ('h \<times> 'h comm) \<Rightarrow> bool\<close> where
  step1[intro!]: \<open>opstep a s s' \<Longrightarrow> opstep_trancl [a] s s'\<close>
| step[intro!]: \<open>opstep a s s' \<Longrightarrow> opstep_trancl as s' s'' \<Longrightarrow> opstep_trancl (a # as) s s''\<close>

inductive opstep_rtrancl :: \<open>act list \<Rightarrow> ('h::perm_alg) \<times> 'h comm \<Rightarrow> ('h \<times> 'h comm) \<Rightarrow> bool\<close> where
  refl[intro!]: \<open>opstep_rtrancl [] s s\<close>
| step[intro!]: \<open>opstep a s s' \<Longrightarrow> opstep_rtrancl as s' s'' \<Longrightarrow> opstep_rtrancl (a # as) s s''\<close>

paragraph \<open> Pretty operational semantics \<close>

abbreviation(input) pretty_opstep_trancl :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sup>+ _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>as\<rightarrow>\<^sup>+ ht \<equiv> opstep_trancl as hs ht\<close>

abbreviation(input) pretty_opstep_rtrancl :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sup>\<star> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>as\<rightarrow>\<^sup>\<star> ht \<equiv> opstep_rtrancl as hs ht\<close>
*)


section \<open> Sugared atomic programs \<close>

definition \<open>passert p \<equiv> \<lambda>a b. p a \<and> a = b\<close>

abbreviation \<open>Assert p \<equiv> Atomic (passert p)\<close>
abbreviation \<open>Assume p \<equiv> Atomic (\<lambda>a. p)\<close>

lemmas Assert_def = arg_cong[where f=Atomic, OF meta_eq_to_obj_eq[OF passert_def]]

lemma passert_simps[simp]:
  \<open>passert p a b \<longleftrightarrow> p a \<and> b = a\<close>
  by (force simp add: passert_def)

lemma opstep_assert[intro!]: \<open>p h \<Longrightarrow> opstep Local (h, Assert p) (h, Skip)\<close>
  by (force simp add: opstep.atomic passert_def)

lemma opstep_assume[intro!]: \<open>q h' \<Longrightarrow> opstep Local (h, Assume q) (h', Skip)\<close>
  by (force simp add: opstep.atomic rel_liftR_def)

subsection \<open> If-then-else and While Loops \<close>

definition \<open>IfThenElse p ct cf \<equiv> Assert p ;; ct \<^bold>+ Assert (-p) ;; cf\<close>
definition \<open>WhileLoop p c \<equiv> (Assert p ;; c)\<^sup>\<star> ;; Assert (-p)\<close>

lemma IfThenElse_inject[simp]:
  \<open>IfThenElse p1 ct1 cf1 = IfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (simp add: IfThenElse_def,
      metis less_le_not_le order_neq_less_conv(2) passert_simps predicate1I)

lemma WhileLoop_inject[simp]:
  \<open>WhileLoop p1 c1 = WhileLoop p2 c2 \<longleftrightarrow> p1 = p2 \<and> c1 = c2\<close>
  by (simp add: WhileLoop_def, metis IfThenElse_def IfThenElse_inject)

lemma IfThenElse_distinct[simp]:
  \<open>IfThenElse p ct cf \<noteq> Skip\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 ;; c2\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 \<parallel> c2\<close>
  \<open>IfThenElse p ct cf \<noteq> c\<^sup>\<star>\<close>
  \<open>IfThenElse p ct cf \<noteq> Atomic b\<close>
  \<open>Skip \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 ;; c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 \<parallel> c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>c\<^sup>\<star> \<noteq> IfThenElse p ct cf\<close>
  \<open>Atomic b \<noteq> IfThenElse p ct cf\<close>
  by (simp add: IfThenElse_def)+

lemma WhileLoop_distinct[simp]:
  \<open>WhileLoop p c \<noteq> Skip\<close>
  \<open>WhileLoop p c \<noteq> c1 \<^bold>+ c2\<close>
  \<open>WhileLoop p c \<noteq> c1 \<parallel> c2\<close>
  \<open>WhileLoop p c \<noteq> c\<^sup>\<star>\<close>
  \<open>WhileLoop p c \<noteq> Atomic b\<close>
  \<open>Skip \<noteq> WhileLoop p c\<close>
  \<open>c1 \<^bold>+ c2 \<noteq> WhileLoop p c\<close>
  \<open>c1 \<parallel> c2 \<noteq> WhileLoop p c\<close>
  \<open>c\<^sup>\<star> \<noteq> WhileLoop p c\<close>
  \<open>Atomic b \<noteq> WhileLoop p c\<close>
  by (simp add: WhileLoop_def)+


lemma opstep_IfThenElse_iff[opstep_iff]:
  \<open>opstep a (h, IfThenElse p ct cf) s' \<longleftrightarrow>
    a = Local \<and> p h \<and> s' = (h, Skip ;; ct) \<or> a = Local \<and> \<not> p h \<and> s' = (h, Skip ;; cf)\<close>
  by (simp add: IfThenElse_def opstep_iff)

lemma opstep_IfThenElse_true[intro]:
  \<open>p h \<Longrightarrow> opstep Local (h, IfThenElse p a b) (h, Skip ;; a)\<close>
  by (simp add: opstep_iff)

lemma opstep_IfThenElse_false[intro]:
  \<open>\<not> p h \<Longrightarrow> opstep Local (h, IfThenElse p a b) (h, Skip ;; b)\<close>
  by (simp add: opstep_iff)

lemma opstep_WhileLoop_iff[opstep_iff]:
  \<open>opstep a (h, WhileLoop p c) s' \<longleftrightarrow>
    (a = Tau \<and> s' = (h, Skip ;; Assert (- p)) \<or>
      a = Tau \<and> s' = (h, ((Assert p ;; c) ;; (Assert p ;; c)\<^sup>\<star>) ;; Assert (- p)))\<close>
  by (force simp add: WhileLoop_def opstep_iff)

lemma opstep_WhileLoop_true[intro]:
  \<open>p h \<Longrightarrow> opstep Tau (h, WhileLoop p c) (h, (((Assert p ;; c) ;; (Assert p ;; c)\<^sup>\<star>) ;; Assert (-p)))\<close>
  by (simp add: opstep_iff)

lemma opstep_WhileLoop_false[intro]:
  \<open>\<not> p h \<Longrightarrow> opstep Tau (h, WhileLoop p c) (h, (((Assert p ;; c) ;; (Assert p ;; c)\<^sup>\<star>) ;; Assert (-p)))\<close>
  by (simp add: opstep_iff)


section \<open> Safe \<close>

inductive safe
  :: \<open>nat \<Rightarrow> (('l::perm_alg) \<times> ('s::perm_alg)) comm \<Rightarrow>
      'l \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('l \<times> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  safe_nil[intro!]: \<open>safe 0 c hl hs r g q\<close>
| safe_suc[intro]:
  \<open>\<comment> \<open> if the command is Skip, the postcondition is established \<close>
    (c = Skip \<longrightarrow> q (hl, hs)) \<Longrightarrow>
    \<comment> \<open> opsteps respect the guarantee \<close>
    (\<And>a c' hl' hs'.
      ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<Longrightarrow>
      (a = Tau \<longrightarrow> (hl, hs) = (hl', hs')) \<and>
      (a = Local \<longrightarrow> g hs hs')) \<Longrightarrow>
    \<comment> \<open> opsteps are locally frame closed \<close>
    (\<And>a c' hl' hs' hlb hlb'.
      ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<Longrightarrow>
      weak_framed_subresource_rel \<top> hl hl' hlb hlb' \<Longrightarrow>
      ((hlb, hs), c) \<midarrow>a\<rightarrow> ((hlb', hs'), c')) \<Longrightarrow>
    \<comment> \<open> opsteps are safe \<close>
    (\<And>a c' hl' hs'.
        ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<Longrightarrow>
        safe n c' hl' hs' r g q) \<Longrightarrow>
    \<comment> \<open> rely steps are safe \<close>
    (\<And>hs'. r hs hs' \<Longrightarrow> safe n c hl hs' r g q) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe (Suc n) c hl hs r g q\<close>

inductive_cases safe_zeroE[elim!]: \<open>safe 0 c hl hs r g q\<close>
inductive_cases safe_sucE[elim]: \<open>safe (Suc n) c hl hs r g q\<close>

subsection \<open> Proofs about safe \<close>

lemma safe_nil_iff[simp]:
  \<open>safe 0 c hl hs r g q \<longleftrightarrow> True\<close>
  by force

lemma safe_suc_iff:
  \<open>safe (Suc n) c hl hs r g q \<longleftrightarrow>
    (c = Skip \<longrightarrow> q (hl, hs)) \<and>
    (\<forall>a c' hl' hs'.
      ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<longrightarrow>
      (a = Tau \<longrightarrow> (hl, hs) = (hl', hs')) \<and>
      (a = Local \<longrightarrow> g hs hs')) \<and>
    (\<forall>a c' hl' hs' hlb hlb'.
      ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<longrightarrow>
      weak_framed_subresource_rel \<top> hl hl' hlb hlb' \<longrightarrow>
      ((hlb, hs), c) \<midarrow>a\<rightarrow> ((hlb', hs'), c')) \<and>
    (\<forall>a c' hl' hs'.
      ((hl, hs), c) \<midarrow>a\<rightarrow> ((hl', hs'), c') \<longrightarrow>
      safe n c' hl' hs' r g q) \<and>
    (\<forall>hl' hs'. r hs hs' \<longrightarrow> safe n c hl hs' r g q)\<close>
  apply (rule iffI)
   apply (erule safe_sucE; fast)
  apply (rule safe_suc; metis)
  done

subsubsection \<open> Monotonicity \<close>

lemma safe_postpred_monoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> q \<le> q' \<Longrightarrow> safe n c hl hs r g q'\<close>
  apply (induct rule: safe.induct)
   apply blast
  apply (simp add: le_fun_def safe_suc; fail)
  done

lemmas safe_postpred_mono = safe_postpred_monoD[rotated]

lemma safe_guarantee_monoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> g \<le> g' \<Longrightarrow> safe n c hl hs r g' q\<close>
  apply (induct rule: safe.induct)
   apply blast
  apply (simp add: le_fun_def safe_suc; fail)
  done

lemmas safe_guarantee_mono = safe_guarantee_monoD[rotated]

lemma safe_rely_antimonoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> r' \<le> r \<Longrightarrow> safe n c hl hs r' g q\<close>
  apply (induct rule: safe.induct)
   apply force
  apply (subst safe_suc_iff, fast)
  done

lemmas safe_rely_antimono = safe_rely_antimonoD[rotated]

lemma safe_step_monoD:
  \<open>safe n c hl hs r g q \<Longrightarrow> m \<le> n \<Longrightarrow> safe m c hl hs r g q\<close>
  apply (induct arbitrary: m rule: safe.inducts)
   apply force
  apply (clarsimp simp add: le_Suc_iff0)
  apply (erule disjE, fast)
  apply clarsimp
  apply (subst safe_suc_iff, force)
  done

subsubsection \<open> Skip \<close>

lemma safe_skip':
  \<open>sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q (hl, hs) \<Longrightarrow> safe n Skip hl hs r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q)\<close>
  apply (induct n arbitrary: hl hs q)
   apply force
  apply (subst safe_suc_iff)
  apply (clarsimp simp add: sp_def)
  apply (meson opstep_skipE rtranclp.rtrancl_into_rtrancl; fail)
  done

lemma safe_skip:
  \<open>p (hl, hs) \<Longrightarrow> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p \<le> q \<Longrightarrow> safe n Skip hl hs r g q\<close>
  apply (rule safe_postpred_monoD[OF safe_skip'[where q=p]])
   apply (metis (mono_tags, lifting) rel_Times_iff rtranclp.rtrancl_refl sp_def)
  apply blast
  done

subsubsection \<open> Atomic \<close>

lemma safe_atom':
  \<open>rel_liftL (wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p) \<sqinter> b \<le> rel_liftR (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q) \<Longrightarrow>
    wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p \<le> pre_state b \<Longrightarrow>
    \<forall>hs'. r\<^sup>*\<^sup>* (snd h) hs' \<longrightarrow> Ex (b h) \<longrightarrow> Ex (b (fst h, hs')) \<Longrightarrow>
    local_frame_safe \<top> b \<Longrightarrow>
    wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (hl, hs) \<Longrightarrow>
    \<forall>hl hs hl' hs'. b (hl, hs) (hl', hs') \<le> g hs hs' \<Longrightarrow>
    safe n (Atomic b) hl hs r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) q)\<close>
  apply (induct n arbitrary: hl hs)
   apply force
  apply clarsimp
  apply (rule safe.safe_suc)
      apply force
     apply (clarsimp simp add: le_fun_def; fail)
    apply (rule opstep_local_frame, blast, fast, force)
   apply (clarsimp, rule safe_skip', fastforce)
  apply (simp add: converse_rtranclp_into_rtranclp wlp_def)
  done

subsubsection \<open> Sequencing \<close>

lemma safe_seq_assoc_left:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    all_atom_comm (local_frame_safe \<top>) c1 \<Longrightarrow>
    c = (c1 ;; c2 ;; c3) \<Longrightarrow>
    safe n ((c1 ;; c2) ;; c3) hl hs r g q\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (subst safe_suc_iff)
  apply (simp add: opstep_iff)
  apply (intro conjI impI allI)
       apply metis
      apply metis
     apply metis
    apply metis
  subgoal
    apply clarsimp
    apply (elim disjE exE conjE, force) (* slow *)
    apply (metis opstep_local_frame rel_lift_top)
    done
  apply (metis opstep_preserves_all_atom_comm)
  done

lemma safe_seq_assoc_right:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    all_atom_comm (local_frame_safe \<top>) c1 \<Longrightarrow>
    c = ((c1 ;; c2) ;; c3) \<Longrightarrow>
    safe n (c1 ;; c2 ;; c3) hl hs r g q\<close>
  apply (induct arbitrary: c1 c2 c3 rule: safe.inducts)
   apply force
  apply (subst safe_suc_iff)
  apply (simp add: opstep_iff)
  apply (intro conjI impI allI)
        apply metis
       apply metis
      apply metis
     apply metis
    apply metis
  subgoal
    apply clarsimp
    apply (metis opstep_local_frame rel_lift_top)
    done
  apply (metis opstep_preserves_all_atom_comm)
  done

lemma safe_seq':
  \<open>safe n c1 hl hs r g q \<Longrightarrow>
    (\<forall>m hl' hs'. m \<le> n \<longrightarrow> q (hl', hs') \<longrightarrow> safe m c2 hl' hs' r g q') \<Longrightarrow>
    safe n (c1 ;; c2) hl hs r g q'\<close>
  apply (induct arbitrary: c2 q' rule: safe.inducts)
   apply force
  apply (rule safe_suc)
      apply blast
     apply (clarsimp simp add: opstep_iff, (elim disjE exE conjE; force))
    apply (simp add: opstep_iff framed_subresource_rel_def, metis)
   apply (simp add: opstep_iff, (elim disjE exE conjE; force))
  apply force
  done

lemma safe_seq:
  \<open>safe n c1 hl hs r g q \<Longrightarrow>
    (\<forall>hl' hs'. q (hl', hs') \<longrightarrow> safe n c2 hl' hs' r g q') \<Longrightarrow>
    safe n (c1 ;; c2) hl hs r g q'\<close>
  by (rule safe_seq', fast, metis safe_step_monoD)

subsection \<open> Iteration \<close>

lemma rtranclp_tuple_rel_semidistrib:
  \<open>(\<lambda>(a, c) (b, d). r1 a b \<and> r2 c d)\<^sup>*\<^sup>* ac bd
    \<Longrightarrow> r1\<^sup>*\<^sup>* (fst ac) (fst bd) \<and> r2\<^sup>*\<^sup>* (snd ac) (snd bd)\<close>
  by (induct rule: rtranclp_induct; force)

lemma rel_Times_rtranclp_semidistrib:
  \<open>(r1 \<times>\<^sub>R r2)\<^sup>*\<^sup>* \<le> r1\<^sup>*\<^sup>* \<times>\<^sub>R r2\<^sup>*\<^sup>*\<close>
  apply (clarsimp simp add: le_fun_def rel_Times_def)
  apply (force dest: rtranclp_tuple_rel_semidistrib)
  done


lemma rtranclp_tuple_lift_eq_left:
  \<open>r2\<^sup>*\<^sup>* c d \<Longrightarrow> (\<lambda>(a, c) (b, d). a = b \<and> r2 c d)\<^sup>*\<^sup>* (a,c) (a,d)\<close>
  by (induct rule: rtranclp_induct, fast, simp add: rtranclp.rtrancl_into_rtrancl)

lemma rtranclp_eq_eq[simp]:
  \<open>(=)\<^sup>*\<^sup>* = (=)\<close>
  by (simp add: rtransp_rel_is_rtransclp)

lemma rel_Times_left_eq_rtranclp_distrib[simp]:
  \<open>((=) \<times>\<^sub>R r2)\<^sup>*\<^sup>* = (=) \<times>\<^sub>R r2\<^sup>*\<^sup>*\<close>
  apply (rule order.antisym)
   apply (force dest: rtranclp_tuple_rel_semidistrib simp add: le_fun_def rel_Times_def)
  apply (force dest: rtranclp_tuple_lift_eq_left simp add: le_fun_def rel_Times_def)
  done

lemma sp_rely_step:
  \<open>r y y' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (x, y) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p (x, y')\<close>
  by (clarsimp simp add: sp_def,
      meson rtranclp.rtrancl_into_rtrancl)

declare eq_OO[simp] OO_eq[simp]

lemma rel_Times_comp[simp]:
  \<open>(a \<times>\<^sub>R b) OO (c \<times>\<^sub>R d) = (a OO c) \<times>\<^sub>R (b OO d)\<close>
  by (force simp add: fun_eq_iff OO_def)

lemmas sp_rely_stronger = sp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]
lemmas sp_rely_absorb =
  sp_comp_rel[where ?r1.0=\<open>(=) \<times>\<^sub>R ra\<^sup>*\<^sup>*\<close> and ?r2.0=\<open>(=) \<times>\<^sub>R rb\<^sup>*\<^sup>*\<close> for ra rb, simplified,
    symmetric]

lemma safe_iter':
  \<open>(\<forall>m hl' hs'. m \<le> n \<longrightarrow> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i (hl', hs') \<longrightarrow> safe m c hl' hs' r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i)) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i (hl, hs) \<Longrightarrow>
    safe n (c\<^sup>\<star>) hl hs r g (sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i)\<close>
  apply (induct n arbitrary: i hl hs)
   apply force
  apply (rule safe_suc)
      apply blast
     apply (force simp add: opstep_iff)
    apply (force simp add: opstep_iff)
    (* subgoal *)
   apply (simp add: le_Suc_eq opstep_iff)
   apply (elim disjE)
    apply (simp add: safe_skip'; fail)
   apply (clarsimp simp add: all_conj_distrib)
   apply (rule_tac q=\<open>sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i\<close> in safe_seq; blast)
    (* done *)
  apply (simp add: le_Suc_eq all_conj_distrib sp_rely_step)
  done


lemma safe_iter:
  \<open>(\<And>n hl hs. p' (hl, hs) \<Longrightarrow> safe n c hl hs r g q') \<Longrightarrow>
    p \<le> i \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i \<le> p' \<Longrightarrow>
    q' \<le> i \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) i \<le> q \<Longrightarrow>
    p (hl, hs) \<Longrightarrow>
    safe n (c\<^sup>\<star>) hl hs r g q\<close>
  apply (rule safe_postpred_mono, assumption)
  apply (rule safe_iter')
   apply (metis (mono_tags) predicate1D safe_postpred_monoD sp_rely_stronger)
  apply (metis predicate1D sp_rely_stronger)
  done

subsubsection \<open> Nondeterminism \<close>

lemma safe_ndet:
  \<open>(\<forall>m\<le>n. safe m c1 hl hs r g q) \<Longrightarrow>
    (\<forall>m\<le>n. safe m c2 hl hs r g q) \<Longrightarrow>
    safe n (c1 \<^bold>+ c2) hl hs r g q\<close>
  apply (induct n arbitrary: c1 c2 hl hs)
   apply blast
  apply (rule safe_suc)
     apply blast
    apply (rule opstep_act_cases)
      apply blast
     apply (force simp add: opstep_iff)
     apply (clarsimp simp add: opstep_iff le_Suc_eq, metis safe_sucE)
  subgoal
    apply (simp add: opstep_iff)
    apply (elim disjE exE conjE; (simp; fail)?) (* 1 \<rightarrow> 4 *)
       apply (metis (no_types, lifting) order.refl safe_sucE)
      apply (metis (no_types, lifting) order.refl safe_sucE)
     apply (metis (no_types, lifting) order.refl safe_sucE)
    apply (metis (no_types, lifting) order.refl safe_sucE)
    done
  subgoal
    apply (clarsimp simp add: opstep_iff le_Suc_eq all_conj_distrib imp_conjR)
    apply (elim safe_sucE)
    apply (metis safe_step_monoD order.refl)
    done
  apply (clarsimp simp add: le_Suc_eq all_conj_distrib)
  apply (subst (asm) safe_suc_iff)+
  apply (metis safe_step_monoD)
  done


subsubsection \<open> Parallel \<close>

lemma framed_subresource_rel_frame_extend_right:
  \<open>\<forall>x. p x \<longrightarrow> x ## hf \<and> p (x + hf) \<Longrightarrow>
    h ## hf \<Longrightarrow>
    h' ## hf \<Longrightarrow>
    framed_subresource_rel p hs hs' h h' \<Longrightarrow>
    framed_subresource_rel p hs hs' (h + hf) (h' + hf)\<close>
  by (clarsimp simp add: framed_subresource_rel_def le_iff_sepadd_weak)
    (meson disjoint_add_swap2 partial_add_assoc2)

lemma framed_subresource_rel_frame_extend_left:
  \<open>\<forall>x. p x \<longrightarrow> hf ## x \<and> p (hf + x) \<Longrightarrow>
    hf ## h \<Longrightarrow>
    hf ## h' \<Longrightarrow>
    framed_subresource_rel p hs hs' h h' \<Longrightarrow>
    framed_subresource_rel p hs hs' (hf + h) (hf + h')\<close>
  using framed_subresource_rel_frame_extend_right
  by (metis disjoint_sym_iff partial_add_commute)




lemma (in perm_alg)
  \<open>x ## y \<Longrightarrow> core_rel x x \<Longrightarrow> core_rel y y \<Longrightarrow> core_rel (x + y) (x + y)\<close>
  unfolding sepadd_dup_def core_rel_def
  by (metis disjoint_add_swap disjoint_middle_swap order_refl partial_add_double_assoc)

lemma (in perm_alg)
  \<open>x ## y \<Longrightarrow> core_rel x cx \<Longrightarrow> core_rel y cy \<Longrightarrow> core_rel (x + y) cxy \<Longrightarrow> cx + cy \<le> cxy\<close>
  unfolding sepadd_dup_def core_rel_def
  by (metis (mono_tags, opaque_lifting) disjoint_preservation2 disjoint_sym_iff order.trans
      partial_add_commute partial_le_plus2 sepadd_right_mono)

lemma safe_parallel_skip:
  \<open>safe n Skip hl1 hs1 (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) \<Longrightarrow>
    safe n Skip hl2 hs2 (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2) \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    hs1 ## hs2 \<Longrightarrow>
    weak_rel_add_preserve ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2) \<Longrightarrow>
    safe n Skip (hl1 + hl2) (hs1 + hs2) r (g1 \<squnion> g2)
      (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2)\<close>
  apply (induct n arbitrary: hl1 hl2 hs1 hs2)
   apply force
  apply (elim safe_sucE)
  apply (rule safe_skip[where p=\<open>(sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1 \<^emph> sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2)\<close>])
   apply (simp add: sepconj_def, blast)
  apply (rule order.trans)
   apply (rule sp_sepconj_semidistrib, blast)
  apply (simp add: weak_framed_rel_mono sp_rely_absorb rel_le_rtranscp_relcompp_absorb)
  done

lemma opstep_strong_unframe_right:
  \<open>opstep a s s' \<Longrightarrow>
    hx ## hf \<Longrightarrow>
    s = (hx + hf, c) \<Longrightarrow>
    s' = (h', c') \<Longrightarrow>
    all_atom_comm (strong_unframe_safe (rel_lift ((=) hf))) c \<Longrightarrow>
    (\<exists>hx'. hx' ## hf \<and> h' = hx' + hf \<and> opstep a (hx, c) (hx', c'))\<close>
  apply (induct arbitrary: hx hf c h' c' rule: opstep.inducts)
               apply (blast+)[13]
  apply (simp add: opstep_iff rel_lift_def inf_fun_def)
  apply (drule_tac strong_unframe_safeD, blast, blast)
  apply blast
  done


lemma opstep_strong_unframe_left:
  \<open>opstep a s s' \<Longrightarrow>
    hf ## hx \<Longrightarrow>
    s = (hf + hx, c) \<Longrightarrow>
    s' = (h', c') \<Longrightarrow>
    all_atom_comm (strong_unframe_safe (rel_lift ((=) hf))) c \<Longrightarrow>
    (\<exists>hx'. hf ## hx' \<and> h' = hf + hx' \<and> opstep a (hx, c) (hx', c'))\<close>
  by (metis disjoint_sym_iff opstep_strong_unframe_right partial_add_commute)

lemma wframe_with_top:
  \<open>(wframe r with \<top>) h h'
    \<longleftrightarrow> (r h h' \<or> (\<exists>hx hx' hf. hx ## hf \<and> hx' ## hf \<and> r hx hx' \<and> h = hx + hf \<and> h' = hx' + hf))\<close>
  by (force simp add: wframe_with_def framed_subresource_rel_def)

lemma wframe_with_top':
  fixes h h' :: \<open>'a::sep_alg\<close>
  shows \<open>(wframe r with \<top>) h h' \<longleftrightarrow>
    (\<exists>hx hx' hf. hx ## hf \<and> hx' ## hf \<and> r hx hx' \<and> h = hx + hf \<and> h' = hx' + hf)\<close>
  by (fastforce simp add: wframe_with_top)

lemma pre_state_wframe_with_top':
  fixes h h' :: \<open>'a::sep_alg\<close>
  shows \<open>pre_state (wframe r with \<top>) h \<longleftrightarrow>
    (\<exists>h' hx hx' hf. hx ## hf \<and> hx' ## hf \<and> r hx hx' \<and> h = hx + hf \<and> h' = hx' + hf)\<close>
  by (fastforce simp add: pre_state_def wframe_with_top)

lemma safe_parallel:
  fixes h1 h2 :: \<open>'a::crosssplit_sep_alg\<close>
  shows                       
  \<open>safe n c1 hl1 hs1 (r \<squnion> g2) g1 (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) \<Longrightarrow>
    safe n c2 hl2 hs2 (r \<squnion> g1) g2 (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2) \<Longrightarrow>
    weak_rel_add_preserve ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)
      (sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1)
      (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2) \<Longrightarrow>
    rel_add_preserve r \<top> \<top> \<Longrightarrow>
    all_atom_comm (local_frame_safe (rel_lift ((=) hl2))) c1 \<Longrightarrow>
    all_atom_comm (local_frame_safe (rel_lift ((=) hl1))) c2 \<Longrightarrow>
    hl1 ## hl2 \<Longrightarrow>
    hs1 ## hs2 \<Longrightarrow>
    safe n (c1 \<parallel> c2) (hl1 + hl2) (hs1 + hs2) r (g1 \<squnion> g2)
      ((sp ((=) \<times>\<^sub>R (r \<squnion> g2)\<^sup>*\<^sup>*) q1) \<^emph> (sp ((=) \<times>\<^sub>R (r \<squnion> g1)\<^sup>*\<^sup>*) q2))\<close>
  apply (induct n arbitrary: c1 c2 hl1 hs1 hl2 hs2)
   apply force
  apply (clarsimp simp add: le_Suc_eq safe_suc_iff[where r=\<open>_ \<squnion> _\<close>]
      all_conj_distrib all_ex_conjL imp_conjR)
  apply (rule safe_suc)
     apply blast
    (* subgoal *)
    apply (clarsimp simp add: opstep_iff)
    apply (intro conjI)
     apply clarsimp
     apply (metis (no_types, lifting) opstep_tau_preserves_heap prod_eq_decompose(2))
    apply clarsimp
    apply (erule disjE)
     apply clarsimp
  apply (frule opstep_local_frame)
(*
      apply (drule_tac x=hx in spec, drule mp, (rule partial_le_part_left; assumption),
      drule spec2, drule mp, assumption)
      apply (metis pre_change_state_mono sup_ge1)
*)
  subgoal sorry
    apply clarsimp
     apply (drule_tac x=hx in spec, drule mp, (rule partial_le_part_right; assumption),
      drule spec2, drule mp, assumption)
     apply (metis pre_change_state_mono sup_ge1)
    (* done *)
    apply (clarsimp simp add: opstep_iff)
    apply (elim disjE exE conjE)
    (* Skip \<parallel> Skip \<rightarrow> Skip *)
      apply (clarsimp simp add: pre_state_def)
      apply (rule safe_parallel_skip; presburger)
    (* c1 \<parallel> c2 \<rightarrow> c1' \<parallel> c2 *)
     apply (erule opstep_act_cases)
      apply clarsimp
      apply (drule_tac x=c1' and y=c2 in meta_spec2, drule_tac x=h1 and y=h2 in meta_spec2)
      apply (drule meta_mp)
  subgoal sorry
      apply blast
     apply clarsimp
     apply (drule spec, drule mp, (rule partial_le_part_left; fast),
      drule spec2, drule mp, assumption)
  oops
     apply clarsimp
     apply (rename_tac h1')
     apply (drule_tac x=c1' and y=c2 in meta_spec2, drule_tac x=h1' and y=h2 in meta_spec2)
     apply (drule meta_mp, metis)
     apply (drule meta_mp, blast)
     apply (drule meta_mp)
  subgoal sorry
     apply (drule meta_mp)
  subgoal sorry
     apply blast
    (* c1 \<parallel> c2 \<rightarrow> c1 \<parallel> c2' *)
    (* subgoal *)
    apply (frule opstep_strong_unframe_left, blast, blast, blast, blast)
    apply clarsimp
    apply (rename_tac h2')
    apply (drule_tac x=c1 and y=c2' in meta_spec2, drule_tac x=h1 and y=h2' in meta_spec2)
    apply (drule meta_mp, fast)
    apply (drule meta_mp, metis)
    apply (drule meta_mp)
  subgoal sorry
    apply (drule meta_mp)
  subgoal sorry
    apply blast
    (* done *)
    (* subgoal *)
   apply (clarsimp simp add: wframe_with_top' all_simps(5)[symmetric] imp_conjL imp_conjR
      all_conj_distrib simp del: all_simps(5))
   apply (drule cross_split, blast, blast, blast)
   apply clarsimp
   apply (rename_tac h1s h1l h2s h2l)
   apply (frule_tac a=h1s and b=h2s in rel_add_preserveD, blast, blast, blast, blast)
   apply clarsimp
   apply (rename_tac h1s' h2s')
   apply (drule_tac x=c1 and y=c2 in meta_spec2,
      drule_tac x=\<open>h1s' + h1l\<close> and y=\<open>h2s' + h2l\<close> in meta_spec2)
   apply (drule meta_mp, metis disjoint_add_leftL disjoint_add_rightL)
   apply (drule meta_mp, metis disjoint_add_leftR disjoint_sym)
   apply (drule meta_mp)
  subgoal sorry
   apply (drule meta_mp)
  subgoal sorry
   apply (drule meta_mp, metis disjoint_add_rightL disjoint_add_swap disjoint_middle_swap)
   apply (metis disjoint_add_leftR disjoint_add_swap2 disjoint_sym partial_add_double_assoc)
    (* done *)
  apply blast
  done


subsubsection \<open> Frame rule \<close>

lemma safe_frame:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    all_atom_comm (frame_pred_extends f) c \<Longrightarrow>
    frame_pred_extends f r \<Longrightarrow>
    frame_pred_safe f g \<Longrightarrow>
    h ## hf \<Longrightarrow>
    f hf \<Longrightarrow>
    safe n c (h + hf) r g (q \<^emph> f)\<close>
proof (induct arbitrary: hf rule: safe.induct)
  case (safe_nil c hl hs r g q)
  then show ?case by fast
next
  case (safe_suc h c q g n r)
(*
  obtain hf' where
    \<open>f hf'\<close>
    \<open>h' ## hf'\<close>
    \<open>opstep a (h + hf, c) (h' + hf', c')\<close>
    using safe_step opstep_frame_pred_extendsD safe_step
    by (metis fst_conv snd_conv)
  moreover then have \<open>safe n c' (h' + hf') r g (q \<^emph> f)\<close>
    using safe_step
    by (metis opstep_preserves_all_atom_comm)
  ultimately *)
  then show ?case
    apply -
    apply (rule safe.safe_suc)
    sorry
qed

(*
lemma safe_frame2:
  \<open>safe n c hl hs r g q \<Longrightarrow>
    all_atom_comm (frame_pred_maintains f) c \<Longrightarrow>
    frame_pred_extends f r \<Longrightarrow>
    frame_pred_closed f g \<Longrightarrow>
    h ## hf \<Longrightarrow>
    f hf \<Longrightarrow>
    safe n c (h + hf) r g (q \<^emph> f)\<close>
proof (induct arbitrary: hf rule: safe.induct)
  case safe_nil
  then show ?case by fast
next
  case (safe_step h c a h' c' g q n r)

  have
    \<open>h' ## hf\<close>
    \<open>opstep a (h + hf, c) (h' + hf, c')\<close>
    using safe_step opstep_frame_pred_maintains opstep_frame_pred_maintains2
    by meson+
  moreover then have \<open>safe n c' (h' + hf) r g (q \<^emph> f)\<close>
    using safe_step
    by (blast dest: opstep_preserves_all_atom_comm)
  ultimately show ?case
    using safe_step.prems safe_step.hyps(1-5)
    apply -
    apply (rule safe.safe_step)
        apply assumption
       apply (blast intro: opstep_frame)
      apply (simp add: frame_pred_closed_def; fail)
     apply (metis sepconj_def)
    apply force
    done
qed
*)


section \<open> Soundness \<close>

text \<open> TODO: move these lemmas \<close>

lemma opstep_tau_extendD:
  \<open>opstep a s s' \<Longrightarrow>
    a = Tau \<Longrightarrow>
    all_atom_comm (\<lambda>b. \<forall>s s'. b s s' \<longrightarrow> (\<forall>sa\<ge>s. \<exists>sa'\<ge>s'. b sa sa')) (snd s) \<Longrightarrow>
    fst s ## h2 \<Longrightarrow>
    \<exists>h''\<ge>fst s'. opstep a (fst s + h2, snd s) (h'', snd s')\<close>
  by (induct rule: opstep.induct)
    (force dest: partial_le_plus)+

lemma can_compute_frame:
  \<open>can_compute s \<Longrightarrow>
    all_atom_comm (\<lambda>b. \<forall>s s'. b s s' \<longrightarrow> (\<forall>sa\<ge>s. \<exists>sa'\<ge>s'. b sa sa')) (snd s) \<Longrightarrow>
    fst s ## r \<Longrightarrow>
    can_compute (fst s + r, snd s)\<close>
  unfolding can_compute_def
  using opstep_tau_extendD
  oops

lemma soundness:
  fixes p q :: \<open>'a::perm_alg \<Rightarrow> bool\<close>
  assumes \<open>rgsat c r g p q\<close>
    and \<open>p h\<close>
  shows \<open>safe n c hl hs r g q\<close>
  using assms
proof (induct c r g p q arbitrary: n h rule: rgsat.inducts)
  case (rgsat_skip p r q g as h)
  then show ?case
    by (force intro!: safe_skip[where p=p])
next
  case (rgsat_iter c r g p' q' p i q)
  then show ?case
    using safe_iter[of p' _ _ _ q' p i]
    by force
next
  case (rgsat_seq c1 r g p1 p2 c2 p3)
  then show ?case
    using safe_seq[of n c1 h r g p2 c2 p3]
    by blast
next
  case (rgsat_ndet c1 r g1 p q1 c2 g2 q2 g q)
  then show ?case
    using safe_ndet[of n c1 hl hs r g q c2]
    by (meson safe_guarantee_mono safe_postpred_mono)
next
  case (rgsat_parallel s1 r g2 g1 p1 q1 s2 p2 q2 g p q)
  moreover obtain h1 h2
    where
      \<open>p1 h1\<close>
      \<open>p2 h2\<close>
      \<open>h = h1 + h2\<close>
      \<open>h1 ## h2\<close>
    using rgsat_parallel
    by (metis predicate1D sepconj_def)
  moreover obtain n1 n2
    where
      \<open>n = n1 + n2\<close>
      \<open>g = g1 \<squnion> g2\<close>
      \<open>safe n1 s1 h1 (r \<squnion> g2) g1 q1\<close>
      \<open>safe n2 s2 h2 (r \<squnion> g1) g2 q2\<close>
    sorry
  ultimately show ?case
    apply clarsimp
    apply (rule safe_postpred_mono, blast)
    apply (rule safe_parallel)
    sorry
next
  case (rgsat_atom p b q Something g p' f r q')
  then show ?case
    sorry
next
  case (rgsat_frame c r g p q f as)
  obtain h1 h2
    where
      \<open>h1 ## h2\<close>
      \<open>h = h1 + h2\<close>
      \<open>p h1\<close>
      \<open>f h2\<close>
    using rgsat_frame.prems
    by (clarsimp simp add: sepconj_def)
  moreover then have \<open>safe as c h1 r g q\<close>
    using rgsat_frame.prems
    apply -
    apply (rule rgsat_frame.hyps(2))
      apply blast
     apply blast
    apply blast
    done
  ultimately show ?case
    using rgsat_frame
    by (force intro!: safe_frame2 simp add: frame_pred_closed_def)
next
  case (rgsat_weaken c r' g' p' q' p q r g)
  then show ?case sorry
qed

end