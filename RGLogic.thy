theory RGLogic
  imports Lang
begin

section \<open> Framed step relation \<close>

context perm_alg
begin

text \<open>
  This predicate ensures that an update between two subresources preserve the rest of the heap.
  We need this in the perm_alg case, when we don't necessarily have a unit.
\<close>

definition
  \<open>framed_subresource_rel p ha ha' h h' \<equiv>
    (\<exists>hf. p hf \<and> ha ## hf \<and> ha' ## hf \<and> h = ha + hf \<and> h' = ha' + hf)\<close>

definition
  \<open>weak_framed_subresource_rel p ha ha' h h' \<equiv>
    ha = h \<and> ha' = h' \<or> framed_subresource_rel p ha ha' h h'\<close>

lemma framed_subresource_relI:
  \<open>p hf \<Longrightarrow> ha ## hf \<Longrightarrow> ha' ## hf \<Longrightarrow> h = ha + hf \<Longrightarrow> h' = ha' + hf \<Longrightarrow>
    framed_subresource_rel p ha ha' h h'\<close>
  by (force simp add: framed_subresource_rel_def)

lemma framed_subresource_rel_refl[intro!]:
  \<open>weak_framed_subresource_rel p h h' h h'\<close>
  by (simp add: weak_framed_subresource_rel_def)

lemma framed_subresource_rel_impl_weak[intro]:
  \<open>framed_subresource_rel p hx hx' h h' \<Longrightarrow> weak_framed_subresource_rel p hx hx' h h'\<close>
  using weak_framed_subresource_rel_def by force

lemma framed_subresource_rel_frame_second:
  \<open>framed_subresource_rel \<top> ha ha' h h' \<Longrightarrow>
    h ## hf \<Longrightarrow>
    h' ## hf \<Longrightarrow>
    framed_subresource_rel \<top> ha ha' (h + hf) (h' + hf)\<close>
  using disjoint_add_swap_lr partial_add_assoc2
  by (simp add: framed_subresource_rel_def, meson)

lemma framed_subresource_rel_frame:
  \<open>framed_subresource_rel \<top> ha ha' h h' \<Longrightarrow>
    h ## hf \<Longrightarrow>
    h' ## hf \<Longrightarrow>
    framed_subresource_rel \<top> ha ha' (h + hf) (h' + hf)\<close>
  using disjoint_add_swap_lr partial_add_assoc2
  by (simp add: framed_subresource_rel_def, meson)

lemma framed_subresource_rel_sym:
  \<open>framed_subresource_rel p a b a' b' \<Longrightarrow> framed_subresource_rel p b a b' a'\<close>
  using framed_subresource_rel_def by auto

lemma framed_subresource_le_firstD[dest]:
  \<open>framed_subresource_rel f ha ha' h h' \<Longrightarrow> ha \<preceq> h\<close>
  using framed_subresource_rel_def partial_le_plus by force

lemma framed_subresource_le_secondD[dest]:
  \<open>framed_subresource_rel f ha ha' h h' \<Longrightarrow> ha' \<preceq> h'\<close>
  using framed_subresource_rel_def partial_le_plus by auto

lemma wframed_subresource_le_firstD[dest]:
  \<open>weak_framed_subresource_rel f ha ha' h h' \<Longrightarrow> ha \<preceq> h\<close>
  using weak_framed_subresource_rel_def by auto

lemma wframed_subresource_le_secondD[dest]:
  \<open>weak_framed_subresource_rel f ha ha' h h' \<Longrightarrow> ha' \<preceq> h'\<close>
  using weak_framed_subresource_rel_def by auto

lemma framed_subresource_rel_top_same_sub_iff[simp]:
  \<open>framed_subresource_rel f a a b b' \<longleftrightarrow> b = b' \<and> (\<exists>xf. a ## xf \<and> b = a + xf \<and> f xf)\<close>
  by (force simp add: framed_subresource_rel_def)

definition \<open>framecl r \<equiv> (\<lambda>a b. (\<exists>x y. r x y \<and> framed_subresource_rel \<top> x y a b))\<close>

lemma framecl_frame_closed:
  \<open>(x ## hf) \<Longrightarrow> (y ## hf) \<Longrightarrow> b x y \<Longrightarrow> framecl b (x + hf) (y + hf)\<close>
  by (force simp add: framecl_def framed_subresource_rel_def)

end

context multiunit_sep_alg
begin

lemma mu_sep_alg_compatible_framed_subresource_rel_iff:
  assumes
    \<open>compatible h h'\<close>
    \<open>p (unitof h)\<close>
  shows
  \<open>weak_framed_subresource_rel p ha ha' h h' \<longleftrightarrow> framed_subresource_rel p ha ha' h h'\<close>
  using assms
  apply (simp add: weak_framed_subresource_rel_def framed_subresource_rel_def)
  apply (metis compatible_then_same_unit unitof_disjoint2 unitof_is_unitR2)
  done

end

lemma (in sep_alg) sep_alg_framed_subresource_rel_iff:
  \<open>p 0 \<Longrightarrow>
    weak_framed_subresource_rel p ha ha' h h' \<longleftrightarrow> framed_subresource_rel p ha ha' h h'\<close>
  by (force simp add: weak_framed_subresource_rel_def framed_subresource_rel_def)


section \<open> Rely-Guarantee Separation Logic \<close>

inductive rgsat ::
  \<open>('l::perm_alg \<times> 's) comm \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    bool\<close>
  where
  rgsat_skip:
  \<open>sswa r p \<le> q \<Longrightarrow> sswa r p \<le> S \<Longrightarrow> rgsat Skip r g p q S F\<close>
| rgsat_iter:
  \<open>rgsat c r g (sswa r i) (sswa r i) (sswa r S) F \<Longrightarrow>
    p \<le> wssa r i \<Longrightarrow>
    sswa r i \<le> q \<Longrightarrow>
    sswa r S \<le> S' \<Longrightarrow>
    rgsat (Iter c) r g p q S' F\<close>
| rgsat_seq:
  \<open>rgsat c1 r g p1 p2 S1 F \<Longrightarrow>
    rgsat c2 r g p2 p3 S2 F \<Longrightarrow>
    S1 \<squnion> S2 \<le> S \<Longrightarrow>
    rgsat (c1 ;; c2) r g p1 p3 S F\<close>
| rgsat_indet:
  \<open>rgsat c1 r g1 p q1 S1 F \<Longrightarrow>
    rgsat c2 r g2 p q2 S2 F \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    q1 \<le> q \<Longrightarrow> q2 \<le> q \<Longrightarrow>
    S1 \<squnion> S2 \<le> S \<Longrightarrow>
    rgsat (c1 \<^bold>+ c2) r g p q S F\<close>
| rgsat_endet:
  \<open>rgsat c1 r g1 p q1 S1 F \<Longrightarrow>
    rgsat c2 r g2 p q2 S2 F \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    q1 \<le> q \<Longrightarrow> q2 \<le> q \<Longrightarrow>
    S1 \<squnion> S2 \<le> S \<Longrightarrow>
    rgsat (c1 \<box> c2) r g p q S F\<close>
| rgsat_par:
  \<open>rgsat s1 (r \<squnion> g2) g1 p1 q1 S1 (S2 \<squnion> S2 \<^emph>\<and> F) \<Longrightarrow>
    rgsat s2 (r \<squnion> g1) g2 p2 q2 S2 (S1 \<squnion> S1 \<^emph>\<and> F) \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    p \<le> p1 \<^emph>\<and> p2 \<Longrightarrow>
    sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2 \<le> q \<Longrightarrow>
    sswa (r \<squnion> g2) S1 \<^emph>\<and> sswa (r \<squnion> g1) S2 \<le> S \<Longrightarrow>
    rgsat (s1 \<parallel> s2) r g p q S F\<close>
| rgsat_atom:
  \<open>p' \<le> wssa r p \<Longrightarrow>
    sswa r q \<le> q' \<Longrightarrow>
    wssa r p \<le> S \<Longrightarrow>
    sswa r q \<le> S \<Longrightarrow>
    wssa r p \<le> ap \<Longrightarrow>
    \<forall>f\<le>F. wssa r p \<^emph>\<and> f \<le> ap \<Longrightarrow>
    sp aq (wssa r p) \<le> q \<Longrightarrow>
    \<forall>f\<le>F. sp aq (wssa r p \<^emph>\<and> f) \<le> q \<^emph>\<and> f \<Longrightarrow>
    rel_liftL (wssa r p) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    \<forall>f\<le>F. rel_liftL (wssa r p \<^emph>\<and> f) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    rgsat (Atomic ap aq) r g p' q' S F\<close>
| rgsat_frame:
  \<open>rgsat c r g p q S F \<Longrightarrow>
    p' \<le> p \<^emph>\<and> f \<Longrightarrow>
    q \<^emph>\<and> sswa (r \<squnion> g) f \<le> q' \<Longrightarrow>
    sswa (r \<squnion> g) f \<le> F \<Longrightarrow>
    F' \<le> sswa (r \<squnion> g) f \<midarrow>\<^emph>\<^sub>\<and> F \<Longrightarrow>
    S \<^emph>\<and> F \<le> S' \<Longrightarrow>
    rgsat c r g p' q' S' F'\<close>
| rgsat_weaken:
  \<open>rgsat c r' g' p' q' S' F' \<Longrightarrow>
    p \<le> p' \<Longrightarrow>
    q' \<le> q \<Longrightarrow>
    r \<le> r' \<Longrightarrow>
    g' \<le> g \<Longrightarrow>
    S' \<le> S \<Longrightarrow>
    F \<le> F' \<Longrightarrow>
    rgsat c r g p q S F\<close>
| rgsat_Disj:
  \<open>p' \<le> \<Squnion>P \<Longrightarrow>
    \<forall>p\<in>P. rgsat c r g p q S F \<Longrightarrow>
    rgsat c r g p' q S F\<close>
| rgsat_Conj:
  \<open>\<forall>q\<in>Q. rgsat c r g p q S F \<Longrightarrow>
    Q \<noteq> {} \<Longrightarrow>
    \<forall>z a b c. F (c, z) \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    \<Sqinter>Q \<le> q' \<Longrightarrow>
    rgsat c r g p q' S F\<close>

abbreviation rgsat_pretty
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close>
  (\<open>_, _ \<turnstile>\<^bsub>_, _\<^esub> { _ } _ { _ }\<close> [55, 55, 0, 0, 55, 55, 55] 56) where
  \<open>r, g \<turnstile>\<^bsub>L, F\<^esub> { p } c { q } \<equiv> rgsat c r g p q L F\<close>

inductive_cases rgsat_skipE[elim]: \<open>rgsat Skip r g p q L F\<close>
inductive_cases rgsat_seqE[elim]: \<open>rgsat (c1 ;; c2) r g p q L F\<close>
inductive_cases rgsat_iterE[elim]: \<open>rgsat (DO c OD) r g p q L F\<close>
inductive_cases rgsat_parE[elim]: \<open>rgsat (c1 \<parallel> c2) r g p q L F\<close>
inductive_cases rgsat_atomE[elim]: \<open>rgsat (Atomic ap aq) r g p q L F\<close>
inductive_cases rgsat_indetE[elim]: \<open>rgsat (c1 \<^bold>+ c2) r g p q L F\<close>
inductive_cases rgsat_endetE[elim]: \<open>rgsat (c1 \<box> c2) r g p q L F\<close>


lemma backwards_done:
  \<open>rgsat Skip r g (wssa r p) p (wssa r p) F\<close>
  by (rule rgsat_weaken[OF rgsat_skip _ _ order.refl order.refl,
        where p'=\<open>wssa r p\<close> and q'=p and S'=\<open>wssa r p\<close> and F'=F])
      (clarsimp simp add: sp_def wlp_def le_fun_def split: sum.split; meson rtranclp_trans)+

lemma rgsat_impossible[intro]:
  \<open>rgsat c r g \<bottom> q L F\<close>
  using rgsat_Disj[of \<open>\<bottom>\<close> \<open>{}\<close>]
  by simp

lemma rgsat_disj:
  \<open>rgsat c r g p1 q L F \<Longrightarrow>
    rgsat c r g p2 q L F \<Longrightarrow>
    rgsat c r g (p1 \<squnion> p2) q L F\<close>
  using rgsat_Disj[of \<open>p1 \<squnion> p2\<close> \<open>{p1,p2}\<close> c]
  by simp

lemma rgsat_conj:
  \<open>rgsat c r g p q1 L F \<Longrightarrow>
    rgsat c r g p q2 L F \<Longrightarrow>
    \<forall>z a b c. F (c, z) \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    rgsat c r g p (q1 \<sqinter> q2) L F\<close>
  using rgsat_Conj[of \<open>{q1,q2}\<close> c _ _ _ _ _ \<open>q1 \<sqinter> q2\<close>]
  by simp

text \<open>
  The strongest weakening rule we can prove by induction.
  This is because the frame rule stabilises not just on \<open>r\<close> (antimono) but also \<open>g\<close> (mono).
  It is nevertheless sound to use the stronger version.
\<close>
lemma rgsat_weak_weaken:
  \<open>rgsat c r g p q S \<top> \<Longrightarrow>
      p' \<le> p \<Longrightarrow>
      q \<le> q' \<Longrightarrow>
      r' \<le> r \<Longrightarrow>
      S \<le> S' \<Longrightarrow>
      rgsat c r' g' p' q' S' \<top>\<close>
proof(induct arbitrary: r' g' p' q' S' rule: rgsat.inducts)
  case (rgsat_skip r p q S g F)
  then show ?case
    by (intro rgsat.rgsat_skip)
      (meson order.trans relyrel_mono sp_mono; fail)+
next
  case (rgsat_iter c r g i L F p q)
  then show ?case
    sorry
(*
    apply (intro rgsat.rgsat_iter[of _ _ _ i L])
       apply (metis order.refl sswa_rel_mono)
      apply (meson order.trans relyrel_mono wlp_rel_antimono; fail)
     apply (meson order.trans relyrel_mono sp_rel_mono; fail)
    apply (meson order.trans relyrel_mono sp_rel_mono; fail)
    done
*)
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
  case (rgsat_frame c r g p q L F p' f q' F' L')
  then show ?case
    sorry
next
  case (rgsat_weaken c ra' ga' pa' qa' Sa' Fa' p q r g S F)

  from rgsat_weaken.hyps(3-) rgsat_weaken.prems
  show ?case
    using rgsat.rgsat_weaken[of c r' g' p' q' S' Fa'] rgsat_weaken.hyps(2)
    by simp
next
  case (rgsat_Disj p' P c r g q L F)
  then show ?case
    using rgsat.rgsat_Disj[of _ P c]
    by simp
next
  case (rgsat_Conj Q c r g p L F q')
  then show ?case
    using rgsat.rgsat_Conj[of Q c]
    by simp
qed
(*
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
    \<open>(=) \<sqinter> rel_liftL (sswa r p \<sqinter> wssa r px) \<le> \<top> \<times>\<^sub>R g\<close>
    \<open>\<forall>f\<le>F. (=) \<sqinter> rel_liftL ((sswa r p \<sqinter> wssa r px) \<^emph>\<and> f) \<le> \<top> \<times>\<^sub>R g\<close>
  shows
    \<open>r, g \<turnstile>\<^bsub>sswa r p \<sqinter> wssa r px, F\<^esub> { p \<sqinter> wssa r px } Assert px { sswa r p \<sqinter> wssa r px }\<close>
  unfolding Assert_def
  apply (rule rgsat_atom[where p=\<open>sswa r p \<sqinter> px\<close> and q=\<open>sswa r p \<sqinter> wssa r px\<close>])
           apply (force simp add: wlp_inf)
          apply (metis order.refl sp_inf_semidistrib sswa_over_sswa_eq sswa_over_wssa_eq)
         apply (force simp add: wlp_inf)
        apply (metis order.refl sp_inf_semidistrib sswa_over_sswa_eq sswa_over_wssa_eq)
       apply blast
      apply (cut_tac assms(1))
      apply (simp add: wlp_inf)
     apply (simp add: wlp_inf; fail)
    apply (simp add: wlp_inf; fail)
   apply (cut_tac assms(2))
   apply (simp add: wlp_inf le_fun_def; fail)
  apply (cut_tac assms(3))
  apply (simp add: wlp_inf le_fun_def; fail)
  done


subsection \<open> Await \<close>

(* TODO *)
lemma rgsat_await':
  assumes
    \<open>\<forall>f\<le>F. (wssa r p \<^emph>\<and> f) \<sqinter> px \<le> (wssa r p \<sqinter> px) \<^emph>\<and> f\<close>
    \<open>(=) \<sqinter> rel_liftL (wssa r p \<sqinter> px) \<le> \<top> \<times>\<^sub>R g\<close>
    \<open>\<forall>f\<le>F. (=) \<sqinter> rel_liftL ((wssa r p \<^emph>\<and> f) \<sqinter> px) \<le> \<top> \<times>\<^sub>R g\<close>
  shows
    \<open>r, g \<turnstile>\<^bsub>wssa r p, F\<^esub> { p } Await px { sswa r (wssa r p \<sqinter> px) }\<close>
  unfolding Await_def
  sorry
(*
  apply (rule rgsat_atom[where p=\<open>wssa r p\<close> and q=\<open>wssa r p \<sqinter> px\<close>])
          apply force
         apply force
        apply (simp; fail)
       apply force
      apply (simp add: rel3_proj13_def; fail)
     apply (simp add: assms(1); fail)
    apply (cut_tac assms(2))
    apply (simp add: le_fun_def; fail)
   apply (cut_tac assms(3))
   apply (simp add: le_fun_def; fail)
  apply blast
  done
*)

lemmas rgsat_await =
  rgsat_weaken[OF rgsat_await' _ _ order.refl order.refl _ order.refl, of _ _ p' for p']


subsection \<open> If-then-else \<close>

lemma rgsat_precond_in_localst:
  \<open>r, g \<turnstile>\<^bsub>L, F\<^esub> { p } c { q } \<Longrightarrow> p \<le> L\<close>
  apply (induct rule: rgsat.inducts)
            apply blast
           apply blast
          apply blast
         apply blast
        apply blast
       apply (meson order_trans sepconj_conj_monoL sepconj_conj_monoR sswa_stronger; fail)
      apply (metis order.trans)
     apply (meson order_trans sepconj_conj_mono sswa_stronger; fail)
    apply blast
   apply fast
  apply blast
  done

lemma rgsat_if_then_else:
  assumes frame_assms:
    \<open>\<forall>f\<le>F. (wssa r p \<^emph>\<and> f) \<sqinter> px \<le> (wssa r p \<sqinter> px) \<^emph>\<and> f\<close>
    \<open>(=) \<sqinter> rel_liftL (wssa r p \<sqinter> px) \<le> \<top> \<times>\<^sub>R g\<close>
    \<open>\<forall>f\<le>F. (=) \<sqinter> rel_liftL ((wssa r p \<^emph>\<and> f) \<sqinter> px) \<le> \<top> \<times>\<^sub>R g\<close>
    \<open>\<forall>f\<le>F. (wssa r p \<^emph>\<and> f) \<sqinter> -px \<le> (wssa r p \<sqinter> -px) \<^emph>\<and> f\<close>
    \<open>(=) \<sqinter> rel_liftL (wssa r p \<sqinter> -px) \<le> \<top> \<times>\<^sub>R g\<close>
    \<open>\<forall>f\<le>F. (=) \<sqinter> rel_liftL ((wssa r p \<^emph>\<and> f) \<sqinter> -px) \<le> \<top> \<times>\<^sub>R g\<close>
    and rgsat_assms:
    \<open>r, g \<turnstile>\<^bsub>L1, F\<^esub> { sswa r (wssa r p \<sqinter> px) } ctt { q1 }\<close>
    \<open>r, g \<turnstile>\<^bsub>L2, F\<^esub> { sswa r (wssa r p \<sqinter> -px) } cff { q2 }\<close>
  shows
    \<open>r, g \<turnstile>\<^bsub>wssa r p \<squnion> L1 \<squnion> L2, F\<^esub> { wssa r p } IfThenElse px ctt cff { q1 \<squnion> q2 }\<close>
  unfolding IfThenElse_def
  sorry
(*
  apply (rule rgsat_endet[OF rgsat_seq rgsat_seq order.refl order.refl,
        where ?L1.0=\<open>wssa r p \<squnion> L1\<close> and ?L2.0=\<open>wssa r p \<squnion> L2\<close>])
          apply (rule rgsat_weaken[OF rgsat_await' order.refl order.refl
        order.refl order.refl order.refl order.refl])
            apply (rule frame_assms)
           apply (rule frame_assms)
          apply (rule frame_assms)
         apply (rule rgsat_assms(1))
        apply order
       apply (rule rgsat_weaken[OF rgsat_await' order.refl order.refl
        order.refl order.refl order.refl order.refl])
         apply (rule frame_assms)
        apply (rule frame_assms)
       apply (rule frame_assms)
      apply (rule rgsat_assms(2))
     apply order
    apply blast
   apply blast
  apply blast
  done
*)

subsection \<open> WhileLoop \<close>

lemma rgsat_while_stable:
  assumes frame_assms:
    \<open>\<forall>f\<le>F. (sswa r i \<^emph>\<and> f) \<sqinter> px \<le> (sswa r i \<sqinter> px) \<^emph>\<and> f\<close>
    \<open>(=) \<sqinter> rel_liftL (sswa r i \<sqinter> px) \<le> \<top> \<times>\<^sub>R g\<close>
    \<open>\<forall>f\<le>F. (=) \<sqinter> rel_liftL ((sswa r i \<^emph>\<and> f) \<sqinter> px) \<le> \<top> \<times>\<^sub>R g\<close>
  and rgsat_assms:
    \<open>r, g \<turnstile>\<^bsub>L, F\<^esub> { sswa r (sswa r i \<sqinter> px) } c { sswa r i }\<close>
  shows
    \<open>r, g \<turnstile>\<^bsub>sswa r (i \<squnion> L), F\<^esub> { i } WhileLoop px c { sswa r i }\<close>
  unfolding WhileLoop_def
  apply (rule rgsat_iter[where i=\<open>sswa r i\<close> and S=\<open>i \<squnion> L\<close>])
     apply (rule rgsat_seq)
       apply (rule rgsat_weaken[OF rgsat_await'[where p=\<open>sswa r i\<close> and r=r] _ order.refl order.refl order.refl _ order.refl])
           apply (simp, rule frame_assms)
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

end