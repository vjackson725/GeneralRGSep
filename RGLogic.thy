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
  \<open>p \<le> wssa R q \<Longrightarrow>
    p \<le> wssa R I \<Longrightarrow>
    C Skip \<Longrightarrow>
    rgsat Skip R G p q I F C\<close>
| rgsat_iter:
  \<open>rgsat c R G (sswa R i) i (sswa R I) F C \<Longrightarrow>
    sswa R p \<le> i \<Longrightarrow>
    sswa R i \<le> q \<Longrightarrow>
    sswa R I \<le> I' \<Longrightarrow>
    C (Iter c) \<Longrightarrow>
    rgsat (Iter c) R G p q I' F C\<close>
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
    C (ca \<^bold>\<sqinter> cb) \<Longrightarrow>
    rgsat (ca \<^bold>\<sqinter> cb) r g p q L F C\<close>
| rgsat_endet:
  \<open>rgsat ca r ga p qa La F C \<Longrightarrow>
    rgsat cb r gb p qb Lb F C \<Longrightarrow>
    ga \<le> g \<Longrightarrow> gb \<le> g \<Longrightarrow>
    qa \<le> q \<Longrightarrow> qb \<le> q \<Longrightarrow>
    La \<squnion> Lb \<le> L \<Longrightarrow>
    C (ca \<^bold>\<box> cb) \<Longrightarrow>
    rgsat (ca \<^bold>\<box> cb) r g p q L F C\<close>
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
  \<open>p' \<le> wssa R p \<Longrightarrow>
    sswa R q \<le> q' \<Longrightarrow>
    wssa R p \<le> I \<Longrightarrow>
    sswa R q \<le> I \<Longrightarrow>
    wssa R p \<^emph>\<and> F \<le> ap \<Longrightarrow>
    \<forall>f\<le>F. sp aq (wssa R p \<^emph>\<and> f) \<le> q \<^emph>\<and> f \<Longrightarrow>
    rel_liftL (wssa R p \<^emph>\<and> F) \<sqinter> aq \<le> \<top> \<times>\<^sub>R G \<Longrightarrow>
    C (Atomic ap aq) \<Longrightarrow>
    rgsat (Atomic ap aq) R G p' q' I F C\<close>
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
inductive_cases rgsat_indetE[elim]: \<open>rgsat (c1 \<^bold>\<sqinter> c2) r g p q L F C\<close>
inductive_cases rgsat_endetE[elim]: \<open>rgsat (c1 \<^bold>\<box> c2) r g p q L F C\<close>

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
    \<open>sswa R p \<^emph>\<and> F \<le> pa\<close>
    \<open>\<forall>f\<le>F. sswa R p \<^emph>\<and> f \<le> wssa R q \<^emph>\<and> f\<close>
    \<open>rel_liftL (sswa R p \<^emph>\<and> F) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    \<open>sswa R p \<le> I\<close>
    \<open>wssa R q \<le> I\<close>
    \<open>C (Assert pa)\<close>
  shows
    \<open>R, G, I, F, C \<turnstile> { p } Assert pa { q }\<close>
  using assms
  unfolding Assert_def
  by (intro rgsat_atom[where p=\<open>sswa R p\<close> and q=\<open>wssa R q\<close>];
      simp add: sswa_weaker wssa_stronger)


subsection \<open> Await \<close>

lemma rgsat_await:
  assumes
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> pa \<le> wssa R q \<^emph>\<and> f\<close>
    \<open>rel_liftL ((sswa R p \<^emph>\<and> F) \<sqinter> pa) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    \<open>sswa R p \<le> I\<close>
    \<open>wssa R q \<le> I\<close>
    \<open>C (Await pa)\<close>
  shows
    \<open>R, G, I, F, C \<turnstile> { p } Await pa { q }\<close>
  using assms
  unfolding Await_def
  apply (intro rgsat_atom[where p=\<open>sswa R p\<close> and q=\<open>wssa R q\<close>])
         apply force
        apply force
       apply (simp add: inf.assoc rel_liftL_conj_distrib; fail)+
  done


subsection \<open> If-then-else \<close>

lemma rgsat_precond_in_localst:
  assumes \<open>R, G, I, F, C \<turnstile> { p } c { q }\<close>
  shows \<open>p \<le> I\<close>
  using assms
proof (induct rule: rgsat.inducts)
  case (rgsat_par c1 r g2 g1 p1 q1 L1 L2 F C c2 p2 q2 g p q L)
  then show ?case
    by (meson order.trans sepconj_conj_mono sswa_weaker)
next
  case (rgsat_frame c r g p q L F C p' f q' F' L')
  then show ?case
    by (meson order.trans sepconj_conj_mono sepimp_conj_sepconj_conj_shunt
        sswa_weaker)
next
  case (rgsat_Disj p' P c r g q L F C)
  then show ?case
    by (meson Sup_le_iff order.trans)
qed blast+

lemma rgsat_if_then_else:
  assumes tt_guard_assms:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> pp \<le> wssa R qa \<^emph>\<and> f\<close>
    \<open>rel_liftL ((sswa R p \<^emph>\<and> F) \<sqinter> pp) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> pp \<le> (sswa R p \<sqinter> wssa R ppt) \<^emph>\<and> f\<close>
    and ff_guard_assms:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> -pp \<le> wssa R qb \<^emph>\<and> f\<close>
    \<open>rel_liftL ((sswa R p \<^emph>\<and> F) \<sqinter> -pp) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> -pp \<le> (sswa R p \<sqinter> wssa R ppf) \<^emph>\<and> f\<close>
    and body_assms:
    \<open>R, G, Ia, F, C \<turnstile> { sswa R p \<sqinter> wssa R ppt } ctt { qa }\<close>
    \<open>R, G, Ib, F, C \<turnstile> { sswa R p \<sqinter> wssa R ppf } cff { qb }\<close>
    and misc_assms:
    \<open>C (Await pp)\<close>
    \<open>C (Await (-pp))\<close>
    \<open>C (Await pp ;; ctt)\<close>
    \<open>C (Await (- pp) ;; cff)\<close>
    \<open>C (IfThenElse pp ctt cff)\<close>
    \<open>sswa R p \<le> I\<close>
    \<open>Ia \<le> I\<close>
    \<open>Ib \<le> I\<close>
    \<open>qa \<le> q\<close>
    \<open>qb \<le> q\<close>
  shows
    \<open>R, G, I, F, C \<turnstile> { p } IfThenElse pp ctt cff { q }\<close>
  using misc_assms
  unfolding IfThenElse_def
proof (intro rgsat_endet[OF rgsat_seq rgsat_seq order.refl order.refl,
      where L=I and La=\<open>sswa R p \<squnion> Ia\<close> and La=\<open>sswa R p \<squnion> Ib\<close>])
  show \<open>R, G, sswa R p, F, C \<turnstile> { p } Await pp { sswa R p \<sqinter> wssa R ppt }\<close>
    using tt_guard_assms misc_assms(1,6-)
    apply (intro rgsat_await)
        apply (simp add: wlp_inf; fail)
       apply force+
    done
  show \<open>R, G, Ia, F, C \<turnstile> { sswa R p \<sqinter> wssa R ppt } ctt { qa }\<close>
    using body_assms
    by blast
  show \<open>R, G, sswa R p, F, C \<turnstile> { p } Await (- pp) { sswa R p \<sqinter> wssa R ppf }\<close>
    using ff_guard_assms misc_assms(2,6-)
    apply (intro rgsat_await)
        apply (simp add: wlp_inf)
       apply force+
    done
  show \<open>R, G, Ib, F, C \<turnstile> { sswa R p \<sqinter> wssa R ppf } cff { qb }\<close>
    using body_assms
    by blast
qed simp+


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


subsection \<open> Atom Variants \<close>

text \<open>
  For the atom rule, show we don't need to conj with the atom-precondition
  in the sp assumption.
\<close>
lemma atom_pre_conj_unecessary:
  \<open>sswa R p \<^emph>\<and> F \<le> pa \<Longrightarrow> f \<le> F \<Longrightarrow> sswa R p \<^emph>\<and> f \<le> pa\<close>
  by (meson order.trans sepconj_conj_monoR)

text \<open>
  For atom, when we use the frame, one might question whether we wish to select \<^emph>\<open>all\<close> subpredicates
  of the frame predicate, or merely each frame in the frame predicate individually. Perhaps
  surprisingly, these two variants turn out to be the same.
\<close>

lemma atom_variant_pointwise_frame:
    \<open>(\<forall>f\<le>F. p \<^emph>\<and> f \<le> ap) \<longleftrightarrow> (\<forall>f. F f \<longrightarrow> p \<^emph>\<and> (=) f \<le> ap)\<close>
    \<open>(\<forall>f\<le>F. sp aq (p \<^emph>\<and> f) \<le> q \<^emph>\<and> f) \<longleftrightarrow> (\<forall>f. F f \<longrightarrow> sp aq (p \<^emph>\<and> (=) f) \<le> q \<^emph>\<and> (=) f)\<close>
    \<open>(\<forall>f\<le>F. rel_liftL (p \<^emph>\<and> f) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g) \<longleftrightarrow>
      (\<forall>f. F f \<longrightarrow> rel_liftL (p \<^emph>\<and> (=) f) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g)\<close>
    apply (clarsimp simp add: le_fun_def sepconj_conj_def, metis)
   apply (rule order.antisym)
    apply (clarsimp simp add: le_fun_def; fail)
   apply (clarsimp simp add: le_fun_def sepconj_conj_def sp_def imp_ex_conjL imp_conjL, blast)
  apply (clarsimp simp add: le_fun_def sepconj_conj_def, fast)
  done

text \<open>
  However, framing only by the frame predicate is not equivalent for every case,
  though it is equivalent in two.
\<close>
lemma atom_variant_compressed_frame:
    \<open>(\<forall>f\<le>F. p \<^emph>\<and> f \<le> ap) \<longleftrightarrow> p \<^emph>\<and> F \<le> ap\<close>
    \<open>(\<forall>f\<le>F. sp aq (p \<^emph>\<and> f) \<le> q \<^emph>\<and> f) \<longrightarrow> (sp aq (p \<^emph>\<and> F) \<le> q \<^emph>\<and> F)\<close>
    \<open>(\<forall>f\<le>F. rel_liftL (p \<^emph>\<and> f) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g) \<longleftrightarrow> rel_liftL (p \<^emph>\<and> F) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g\<close>
    apply (clarsimp simp add: le_fun_def sepconj_conj_def, fast)
   apply (clarsimp simp add: le_fun_def sepconj_conj_def sp_def imp_conjL imp_ex_conjL; fail)
  apply (rule order.antisym; simp add: le_fun_def sepconj_conj_def imp_conjL imp_ex_conjL; metis)
  done

lemma atom_variant_compressed_frame2_nequiv:
  \<open>(sp aq (wssa r p \<^emph>\<and> F) \<le> q \<^emph>\<and> F) \<longrightarrow> (\<forall>f\<le>F. sp aq (wssa r p \<^emph>\<and> f) \<le> q \<^emph>\<and> f)\<close>
  nitpick[card 'a=1, card 'b=2]
  oops

lemma Sup_sepconjConj_framest_equiv_sepconjConj_frame:
  \<open>\<Squnion>{wssa R p \<^emph>\<and> f|f. f \<le> F} = (wssa R p \<^emph>\<and> F)\<close>
  apply (simp add: fun_eq_iff sepconj_conj_def)
  apply (intro iffI allI)
   apply (meson predicate1D; fail)
  apply clarsimp
  apply (rename_tac ss sl sf)
  apply (rule_tac
      x=\<open>\<lambda>(slf', ss'). (\<exists>sl. wssa R p (sl, ss') \<and> sl ## sf \<and> slf' = sl + sf) \<and> ss' = ss\<close> in
      exI)
  apply clarsimp
  apply (rule conjI[rotated], blast)
  apply (rule_tac x=\<open>(=) (sf, ss)\<close> in exI)
  apply blast
  done

lemma guar_rel_helper:
  \<open>\<Squnion>{rel_liftL (wssa R p \<^emph>\<and> f) \<sqinter> aq|f. f \<le> F} = rel_liftL (wssa R p \<^emph>\<and> F) \<sqinter> aq\<close>
proof -
  have \<open>\<Squnion>{rel_liftL (wssa R p \<^emph>\<and> f) \<sqinter> aq|f. f \<le> F} =
    \<Squnion>((\<lambda>x. rel_liftL x \<sqinter> aq) ` {wssa R p \<^emph>\<and> f|f. f \<le> F})\<close>
    by (clarsimp simp add: image_def, blast)
  also have \<open>... = rel_liftL (\<Squnion>{wssa R p \<^emph>\<and> f|f. f \<le> F}) \<sqinter> aq\<close>
    by (simp add: fun_eq_iff)
  ultimately show ?thesis
    by (simp add: Sup_sepconjConj_framest_equiv_sepconjConj_frame)
qed

end