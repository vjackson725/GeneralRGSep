theory RGLogic
  imports Lang
begin


section \<open> Rely-Guarantee Separation Logic \<close>

inductive rgsat ::
  \<open>('l::pre_perm_alg \<times> 's) comm \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    (('l \<times> 's) comm \<Rightarrow> bool) \<Rightarrow>
    bool\<close>
  where
  rgsat_skip:
  \<open>sswa r p \<le> q \<Longrightarrow>
    q \<le> L \<Longrightarrow>
    C Skip \<Longrightarrow>
    rgsat Skip r g p q L F C\<close>
| rgsat_iter:
  \<open>rgsat c r g (sswa r i) (sswa r i) (sswa r L) F C \<Longrightarrow>
    p \<le> wssa r i \<Longrightarrow>
    sswa r i \<le> q \<Longrightarrow>
    sswa r L \<le> L' \<Longrightarrow>
    C (Iter c) \<Longrightarrow>
    rgsat (Iter c) r g p q L' F C\<close>
| rgsat_seq:
  \<open>rgsat ca r g p pp La F C \<Longrightarrow>
    rgsat cb r g pp q Lb F C \<Longrightarrow>
    La \<squnion> Lb \<le> L \<Longrightarrow>
    C (ca ;; cb) \<Longrightarrow>
    rgsat (ca ;; cb) r g p q L F C\<close>
| rgsat_indet:
  \<open>rgsat ca r ga p qa La F C \<Longrightarrow>
    rgsat cb r gb p qb Lb F C \<Longrightarrow>
    ga \<le> g \<Longrightarrow> gb \<le> g \<Longrightarrow>
    qa \<le> q \<Longrightarrow> qb \<le> q \<Longrightarrow>
    La \<squnion> Lb \<le> L \<Longrightarrow>
    C (ca \<^bold>+ cb) \<Longrightarrow>
    rgsat (ca \<^bold>+ cb) r g p q L F C\<close>
| rgsat_endet:
  \<open>rgsat ca r ga p qa La F C \<Longrightarrow>
    rgsat cb r gb p qb Lb F C \<Longrightarrow>
    ga \<le> g \<Longrightarrow> gb \<le> g \<Longrightarrow>
    qa \<le> q \<Longrightarrow> qb \<le> q \<Longrightarrow>
    La \<squnion> Lb \<le> L \<Longrightarrow>
    C (ca \<box> cb) \<Longrightarrow>
    rgsat (ca \<box> cb) r g p q L F C\<close>
| rgsat_par:
  \<open>rgsat c1 (r \<squnion> g2) g1 p1 q1 L1 (L2 \<^emph>\<and> F) C \<Longrightarrow>
    rgsat c2 (r \<squnion> g1) g2 p2 q2 L2 (L1 \<^emph>\<and> F) C \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    p \<le> p1 \<^emph>\<and> p2 \<Longrightarrow>
    sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2 \<le> q \<Longrightarrow>
    sswa (r \<squnion> g2) L1 \<^emph>\<and> sswa (r \<squnion> g1) L2 \<le> L \<Longrightarrow>
    C (c1 \<parallel> c2) \<Longrightarrow>
    rgsat (c1 \<parallel> c2) r g p q L F C\<close>
| rgsat_atom:
  \<open>p' \<le> wssa r p \<Longrightarrow>
    sswa r q \<le> q' \<Longrightarrow>
    wssa r p \<le> L \<Longrightarrow>
    sswa r q \<le> L \<Longrightarrow>
    \<forall>f\<le>F. wssa r p \<^emph>\<and> f \<le> ap \<Longrightarrow>
    \<forall>f\<le>F. sp aq (wssa r p \<^emph>\<and> f) \<le> q \<^emph>\<and> f \<Longrightarrow>
    \<forall>f\<le>F. rel_liftL (wssa r p \<^emph>\<and> f) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    C (Atomic ap aq) \<Longrightarrow>
    rgsat (Atomic ap aq) r g p' q' L F C\<close>
| rgsat_frame:
  \<open>rgsat c r g p q L F C \<Longrightarrow>
    p' \<le> p \<^emph>\<and> f \<Longrightarrow>
    q \<^emph>\<and> sswa (r \<squnion> g) f \<le> q' \<Longrightarrow>
    F' \<^emph>\<and> sswa (r \<squnion> g) f \<le> F \<Longrightarrow>
    L \<le> sswa (r \<squnion> g) f \<midarrow>\<^emph>\<^sub>\<and> L' \<Longrightarrow>
    rgsat c r g p' q' L' F' C\<close>
| rgsat_weaken:
  \<open>rgsat c r' g' p' q' L' F' C \<Longrightarrow>
    p \<le> p' \<Longrightarrow>
    q' \<le> q \<Longrightarrow>
    r \<le> r' \<Longrightarrow>
    g' \<le> g \<Longrightarrow>
    L' \<le> L \<Longrightarrow>
    F \<le> F' \<Longrightarrow>
    rgsat c r g p q L F C\<close>
| rgsat_Disj:
  \<open>p' \<le> \<Squnion>P \<Longrightarrow>
    \<forall>p\<in>P. rgsat c r g p q L F C \<Longrightarrow>
    rgsat c r g p' q L F C\<close>
| rgsat_Conj:
  \<open>\<forall>q\<in>Q. rgsat c r g p q L F C \<Longrightarrow>
    Q \<noteq> {} \<Longrightarrow>
    \<forall>z a b f. F (f, z) \<longrightarrow> a ## f \<longrightarrow> b ## f \<longrightarrow> a + f = b + f \<longrightarrow> a = b \<Longrightarrow>
    \<Sqinter>Q \<le> q' \<Longrightarrow>
    rgsat c r g p q' L F C\<close>

abbreviation rgsat_pretty
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_, _, _, _, _ \<turnstile> { _ } _ { _ }\<close> [55, 0, 0, 0, 0, 55, 55, 55] 56) where
  \<open>r, g, L, F, C \<turnstile> { p } c { q } \<equiv> rgsat c r g p q L F C\<close>

inductive_cases rgsat_skipE[elim]: \<open>rgsat Skip r g p q L F C\<close>
inductive_cases rgsat_seqE[elim]: \<open>rgsat (c1 ;; c2) r g p q L F C\<close>
inductive_cases rgsat_iterE[elim]: \<open>rgsat (DO c OD) r g p q L F C\<close>
inductive_cases rgsat_parE[elim]: \<open>rgsat (c1 \<parallel> c2) r g p q L F C\<close>
inductive_cases rgsat_atomE[elim]: \<open>rgsat (Atomic ap aq) r g p q L F C\<close>
inductive_cases rgsat_indetE[elim]: \<open>rgsat (c1 \<^bold>+ c2) r g p q L F C\<close>
inductive_cases rgsat_endetE[elim]: \<open>rgsat (c1 \<box> c2) r g p q L F C\<close>

lemma rgsat_skip_forwards:
  \<open>C Skip \<Longrightarrow> rgsat Skip r g p (sswa r p) (sswa r p) F C\<close>
  by (rule rgsat_skip) force+

lemma rgsat_skip_backwards:
  \<open>C Skip \<Longrightarrow> rgsat Skip r g (wssa r q) q q F C\<close>
  by (rule rgsat_weaken[OF rgsat_skip _ _ order.refl order.refl,
        where p'=\<open>wssa r q\<close> and q'=q and L'=q and F'=F]) force+

lemma rgsat_impossible[intro]:
  \<open>rgsat c r g \<bottom> q L F C\<close>
  using rgsat_Disj[of \<open>\<bottom>\<close> \<open>{}\<close>]
  by simp

lemma rgsat_disj:
  \<open>rgsat c r g p1 q L F C \<Longrightarrow>
    rgsat c r g p2 q L F C \<Longrightarrow>
    rgsat c r g (p1 \<squnion> p2) q L F C\<close>
  using rgsat_Disj[of \<open>p1 \<squnion> p2\<close> \<open>{p1,p2}\<close> c]
  by simp

lemma rgsat_conj:
  \<open>rgsat c r g p q1 L F C \<Longrightarrow>
    rgsat c r g p q2 L F C \<Longrightarrow>
    \<forall>z a b c. F (c, z) \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    rgsat c r g p (q1 \<sqinter> q2) L F C\<close>
  using rgsat_Conj[of \<open>{q1,q2}\<close> c _ _ _ _ _ _ \<open>q1 \<sqinter> q2\<close>]
  by simp

(*
text \<open>
  The strongest weakening rule we can prove by induction.
  This is because the frame rule stabilises not just on \<open>r\<close> (antimono) but also \<open>g\<close> (mono).
  It is nevertheless sound to use the stronger version.
\<close>
lemma rgsat_weak_weaken:
  \<open>rgsat c r g p q L \<top> \<Longrightarrow>
      p' \<le> p \<Longrightarrow>
      q \<le> q' \<Longrightarrow>
      r' \<le> r \<Longrightarrow>
      L \<le> S' \<Longrightarrow>
      rgsat c r' g' p' q' S' \<top>\<close>
proof(induct arbitrary: r' g' p' q' S' rule: rgsat.inducts)
  case (rgsat_skip r p q L g F)
  then show ?case
    by (intro rgsat.rgsat_skip)
      (meson order.trans relyrel_mono sp_mono; fail)+
next
  case (rgsat_iter c r g i L F C p q)
  then show ?case
    sorry
    apply (intro rgsat.rgsat_iter[of _ _ _ i L])
       apply (metis order.refl sswa_rel_mono)
      apply (meson order.trans relyrel_mono wlp_rel_antimono; fail)
     apply (meson order.trans relyrel_mono sp_rel_mono; fail)
    apply (meson order.trans relyrel_mono sp_rel_mono; fail)
    done
next
  case (rgsat_seq c1 r g p1 p2 S1 F c2 p3 S2 L)
  then show ?case
    apply (intro rgsat.rgsat_seq[where ?S1.0=S1 and ?S2.0=S2])
      apply blast
     apply force
    apply order
    done
next
  case (rgsat_indet c1 r g1 p q1 L1 F c2 g2 q2 L2 g q L)
  
  show ?case
    using rgsat_indet.prems rgsat_indet.hyps(5-)
      rgsat.rgsat_indet[OF rgsat_indet.hyps(2) rgsat_indet.hyps(4)]
    by (meson order_refl order_trans)
next
  case (rgsat_endet c1 r g1 p q1 L1 F c2 g2 q2 L2 g q L)

  show ?case
    using rgsat_endet.prems rgsat_endet.hyps(5-)
      rgsat.rgsat_endet[OF rgsat_endet.hyps(2) rgsat_endet.hyps(4)]
    by (meson order_refl order_trans)
next
  case (rgsat_par s1 r g2 g1 p1 q1 S1 S2 F s2 p2 q2 g p q S)
  
  show ?case
    using rgsat_par.prems rgsat_par.hyps(5-)
    apply (intro rgsat.rgsat_par[OF rgsat_par.hyps(2) rgsat_par.hyps(4)])
    sorry
next
  case (rgsat_atom p' r p q q' ap F aq g L)
  then show ?case
    sorry
next
  case (rgsat_frame c r g p q L F C p' f q' F' L')
  then show ?case
    sorry
next
  case (rgsat_weaken c ra' ga' pa' qa' Sa' Fa' p q r g L F C)

  from rgsat_weaken.hyps(3-) rgsat_weaken.prems
  show ?case
    using rgsat.rgsat_weaken[of c r' g' p' q' S' Fa'] rgsat_weaken.hyps(2)
    by simp
next
  case (rgsat_Disj p' P c r g q L F C)
  then show ?case
    using rgsat.rgsat_Disj[of _ P c]
    by simp
next
  case (rgsat_Conj Q c r g p L F C q')
  then show ?case
    using rgsat.rgsat_Conj[of Q c]
    by simp
qed
    (* par *)
       apply (rule_tac ?p1.0=p1 and ?p2.0=p2 and ?q1.0=q1 and ?q2.0=q2 and ?g1.0=g1 and ?g2.0=g2
      and ?L1.0=L1 and ?L2.0=L2 and ?F1.0=F1 and ?F2.0=F2 in rgsat.rgsat_par)
              apply (meson order.refl sup_mono; fail)
             apply (meson order.refl sup_mono; fail)
            apply order
           apply order
          apply order
         apply (meson order.trans le_disj_eq_absorb relyrel_mono sepconj_conj_mono sp_mono
      sup_mono; fail)
        apply order
       apply order
    (* atom *)
     apply (rule_tac p=p and q=q in rgsat_atom)
             apply (meson order.trans rel_Times_mono_right rtranclp_mono wlp_rel_antimono; fail)
            apply (meson order.trans rel_Times_mono_right rtranclp_mono sp_rel_mono; fail)
           apply (meson order.trans rel_Times_mono_right rtranclp_mono sp_rel_mono; fail)
          apply (intro allI impI, drule spec, drule mp, assumption)
          apply (meson order.trans rel_Times_mono_right rtranclp_mono sepconj_conj_monoL sp_pred_mono
      sp_rel_mono; fail)
         apply (meson order.trans rel_Times_mono_right rtranclp_mono sp_rel_mono wlp_rel_antimono
      inf_mono order_le_less sp_pred_mono; fail)
        apply (intro allI impI, drule spec, drule mp, assumption)
        apply (meson order.trans rel_Times_mono_right rtranclp_mono sp_rel_mono wlp_rel_antimono
      sepconj_conj_monoL sp_pred_mono; fail)
       apply (meson order.trans inf_mono le_disj_eq_absorb liftL_mono relyrel_mono sp_rel_mono; fail)
      apply blast
     apply (simp; fail)
    (* frame *)
     apply (rule_tac p=p and q=q and r=ra in rgsat.rgsat_frame)
          apply blast
         apply (rule order.trans; assumption)
        apply (meson order.trans le_disj_eq_absorb sepconj_conj_monoR sswa_rel_mono sup.mono; fail)
       apply (meson order.refl order.trans sp_rel_mono relyrel_mono sup_mono; fail)
      apply (meson order.trans le_disj_eq_absorb sepimp_conj_mono sswa_rel_mono sup.mono)
     apply (simp; fail)
  done
*)


section \<open> Specialised Rules \<close>

subsection \<open> Assert \<close>

lemma rgsat_assert:
  assumes
    \<open>\<forall>f\<le>F. (sswa r p \<sqinter> wssa r px) \<^emph>\<and> f \<le> px\<close>
    \<open>\<forall>f\<le>F. (=) \<sqinter> rel_liftL ((sswa r p \<sqinter> wssa r px) \<^emph>\<and> f) \<le> \<top> \<times>\<^sub>R g\<close>
    \<open>C (Assert px)\<close>
  shows
    \<open>r, g, sswa r p \<sqinter> wssa r px, F, C \<turnstile>
      { p \<sqinter> wssa r px } Assert px { sswa r p \<sqinter> wssa r px }\<close>
  unfolding Assert_def
  apply (rule rgsat_atom[where p=\<open>sswa r p \<sqinter> px\<close> and q=\<open>sswa r p \<sqinter> wssa r px\<close>])
         apply (force simp add: wlp_inf)
        apply (metis order.refl sp_inf_semidistrib sswa_over_sswa_eq sswa_over_wssa_eq)
       apply (force simp add: wlp_inf)
      apply (metis order.refl sp_inf_semidistrib sswa_over_sswa_eq sswa_over_wssa_eq)
     apply (cut_tac assms(1))
     apply (simp add: wlp_inf; fail)
    apply (simp add: wlp_inf; fail)
   apply (cut_tac assms(2))
   apply (simp add: wlp_inf le_fun_def; fail)
  apply (metis Assert_def assms(3))
  done


subsection \<open> Await \<close>

lemma rgsat_await':
  assumes
    \<open>\<forall>f\<le>F. (wssa r p \<^emph>\<and> f) \<sqinter> px \<le> (wssa r p \<sqinter> px) \<^emph>\<and> f\<close>
    \<open>\<forall>f\<le>F. (=) \<sqinter> rel_liftL ((wssa r p \<^emph>\<and> f) \<sqinter> px) \<le> \<top> \<times>\<^sub>R g\<close>
    \<open>C (Await px)\<close>
  shows
    \<open>r, g, wssa r p, F, C \<turnstile>
      { wssa r p } Await px { sswa r (wssa r p \<sqinter> px) }\<close>
  unfolding Await_def
  apply (rule rgsat_atom[where p=\<open>wssa r p\<close> and q=\<open>wssa r p \<sqinter> px\<close>])
         apply force
        apply force
       apply force
      apply (metis inf.cobounded1 relyrel_trans sp_rel_liftL_iff(2) sp_wlp_weak_absorb
      transp_subrel_compp_smaller(2))
     apply blast
    apply (simp add: assms(1); fail)
   apply (cut_tac assms(2))
  apply (simp add: inf_assoc inf_commute rel_liftL_conj_distrib; fail)
  apply (metis Await_def assms(3))
  done

lemmas rgsat_await =
  rgsat_weaken[OF rgsat_await' _ _ order.refl order.refl _ order.refl, of _ _ p' for p']


subsection \<open> If-then-else \<close>

lemma rgsat_precond_in_localst:
  \<open>r, g, L, F, C \<turnstile> { p } c { q } \<Longrightarrow> p \<le> L\<close>
  apply (induct rule: rgsat.inducts)
            apply blast
           apply blast
          apply blast
         apply blast
        apply blast
       apply (meson order.trans sepconj_conj_mono sswa_stronger; fail)
      apply blast
     apply (simp add: sepimp_conj_sepconj_conj_shunt)
     apply (meson order.trans sepconj_conj_mono sswa_stronger; fail)
    apply (meson order_trans sepconj_conj_mono sswa_stronger; fail)
   apply fast
  apply blast
  done

lemma rgsat_if_then_else:
  assumes frame_assms:
    \<open>\<forall>f\<le>F. (wssa r p \<^emph>\<and> f) \<sqinter> px \<le> (wssa r p \<sqinter> px) \<^emph>\<and> f\<close>
    \<open>\<forall>f\<le>F. (wssa r p \<^emph>\<and> f) \<sqinter> -px \<le> (wssa r p \<sqinter> -px) \<^emph>\<and> f\<close>
    \<open>\<forall>f\<le>F. (=) \<sqinter> rel_liftL ((wssa r p \<^emph>\<and> f) \<sqinter> px) \<le> \<top> \<times>\<^sub>R g\<close>
    \<open>\<forall>f\<le>F. (=) \<sqinter> rel_liftL ((wssa r p \<^emph>\<and> f) \<sqinter> -px) \<le> \<top> \<times>\<^sub>R g\<close>
    and rgsat_assms:
    \<open>r, g, wssa r p \<squnion> La, F, C \<turnstile> { sswa r (wssa r p \<sqinter> px) } ctt { q1 }\<close>
    \<open>r, g, wssa r p \<squnion> Lb, F, C \<turnstile> { sswa r (wssa r p \<sqinter> -px) } cff { q2 }\<close>
    and comm_assms:
    \<open>C (Await px)\<close>
    \<open>C (Await (- px))\<close>
    \<open>C (Await px ;; ctt)\<close>
    \<open>C (Await (- px) ;; cff)\<close>
  shows
    \<open>r, g, wssa r p \<squnion> La \<squnion> Lb, F, C \<turnstile> { wssa r p } IfThenElse px ctt cff { q1 \<squnion> q2 }\<close>s
  unfolding IfThenElse_def
  sorry
(*
  thm rgsat_endet[OF rgsat_seq rgsat_seq order.refl order.refl]
  apply (rule rgsat_endet[OF rgsat_seq rgsat_seq order.refl order.refl,
        where ?La4=\<open>wssa r p \<squnion> La\<close> and ?Lb4=\<open>wssa r p \<squnion> Lb\<close>
          and ?ca4=\<open>Await (-px)\<close> and ?cb4=\<open>cff\<close> and ?ca3=\<open>Await (px)\<close> and ?cb3=\<open>ctt\<close>])
             apply (rule rgsat_await[OF frame_assms(2,4)])

             apply (rule rgsat_await[OF frame_assms(1)])

               apply (meson order.refl le_infI1 relyrel_trans sp_wlp_weak_absorb transp_subrel_compp_smaller(1)
      wlp_weaker_iff_sp_stronger; fail)

sorry
*)

subsection \<open> WhileLoop \<close>

lemma rgsat_while_stable:
  assumes frame_assms:
    \<open>\<forall>f\<le>F. (sswa r i \<^emph>\<and> f) \<sqinter> px \<le> (sswa r i \<sqinter> px) \<^emph>\<and> f\<close>
    \<open>\<forall>f\<le>F. (=) \<sqinter> rel_liftL ((sswa r i \<^emph>\<and> f) \<sqinter> px) \<le> \<top> \<times>\<^sub>R g\<close>
    and rgsat_assms:
    \<open>r, g, L, F, C \<turnstile> { sswa r (sswa r i \<sqinter> px) } c { sswa r i }\<close>
  shows
    \<open>r, g, sswa r (i \<squnion> L), F, C \<turnstile> { i } WhileLoop px c { sswa r i }\<close>
  unfolding WhileLoop_def
(*
  apply (rule rgsat_iter[where i=\<open>sswa r i\<close> and S=\<open>i \<squnion> L\<close>])
     apply (rule rgsat_seq)
       apply (rule rgsat_weaken[OF rgsat_await'[where p=\<open>sswa r i\<close> and r=r] _ order.refl order.refl order.refl _ order.refl])
          apply (simp, rule frame_assms)
         apply (simp, rule frame_assms)
        apply force
       apply (simp, rule order.refl)
      apply (simp, rule rgsat_assms)
     apply (meson le_sup_iff sp_pred_mono sswa_stronger sup.cobounded1)
    apply force
   apply force
  apply force
  done
*)
  sorry

end